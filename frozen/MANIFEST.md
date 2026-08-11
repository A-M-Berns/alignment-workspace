# Frozen inputs

**Immutable.** Everything here is read-only, checksummed in
`FROZEN_INPUT_CHECKSUMS.json`, and cited by path — never edited, and never
unpacked into `projects/`. Each input is an **extracted tree**, not an archive,
so it is browsable and every claim in it is citable by path and line.

CI recomputes the tree hashes on every push and fails on drift, and refuses any
pull request that touches this directory unless the same pull request updates
this file. That gate cannot be argued with, which is the point.

| name | date | archive sha256 | tree sha256 | files | description | cited by |
|---|---|---|---|---|---|---|
| `consolidation_aug9/` | 2026-08-09, corrections folded in 2026-08-10 | `5f3bf1bee88fdb8808b3d976358e32f2e21e93f4cb2041d79cc3e0c90f0ba0cc` | `a2ca95ad9d6cafcaecb77b7b4d7a0d75f9a33738e3ecb65437b50a56eb7a164a` | 59 | The consolidation of the leverage line: six theory parts numbered 7–12, a ledger of 180 claims with hypotheses, statuses, sharpness and dependencies, and a trust audit separating machine-checked from hand-derived from transcribed from reading-audit from assumed. **Vendors the August 8 consolidation internally**, at `vendor/consolidation_aug8.zip`, together with the settlement-interface documents and the source tree's own theory documents — all frozen by digest inside it. Verifies standalone. | `projects/leverage/`; `OPEN_PROBLEMS.md` items 1–6; CI's foundations-verification gate |
| `deference-note-dump-2026-06-27/` | 2026-06-27 | `bc51a91b84241128380286b1a8f052a5dde01a90876dc6359cf9b6e3c9aef362` | `722b687a49a7e5f5f2ff2b8e7674fb92697d9cbf30f4f9f8b155dbb0ca48cfc1` | 41 | The delegation line's recorded starting point: research notes across six versions, a statement-level Lean audit, and the Lean development (deference, self-referential target, frozen deliberation, faithful acceleration, tower and acceleration). | `projects/delegation/`; `OPEN_PROBLEMS.md` items 7–9 |
| `references-citations-2026-08-11/` | 2026-08-11 | n/a — created in-repo | `268fbdba885f2d0645d8ea4d5f2887cf249f6ed3bd2fcd1a64f42bbff7bf291c` | 1 | Bibliographic entries and sha256 digests for the third-party papers removed from the two note dumps. Supersedes their `references/` payloads only. | `frozen/MANIFEST.md`; both note-dump entries |
| `dose-response-note-dump-2026-07-02/` | 2026-07-02 | `a69f8a9876b24dd0a2cd0b609e294c53fef0b2596c79f0037812a6a47a60e890` | `d34afa3ce288855517fb9d164adbbaa760aefe8fbf38897c130234a94ae00355` | 13 | Dose-response structure in the deference setting, with its own audit. | `projects/delegation/` |

## Third-party material — resolved 2026-08-11

The note-dump bundles vendored published third-party papers under `references/`.
**This repository has no redistribution rights to them**, so the payloads were
removed and replaced by a citations entry that pins each removed file by sha256 —
the frozen record still says exactly which document the conversations engaged
with, without carrying it. Cite, do not vendor.

This is the one sanctioned way frozen content changes: a new dated entry, the
superseded entries annotated, digests recomputed, all in one change that requires
maintainer review by construction. The bundles' conversations, notes and Lean
content are untouched.

One citation could not be verified against a publisher of record and is flagged
as unverified inside the entry rather than reconstructed.

Both note-dump bundles contain published third-party papers under
`references/`: two papers with their PDFs and extracted text, and the Logical
Induction paper's own source. **Whether this repository may redistribute them is
an author decision and is unresolved.**

The default applied here, and it is deliberate: **keep the bundles intact and
raise the flag.** The bundles are provenance — a note dump with its references
removed is a different artifact, and pruning one unilaterally would both damage
the record and make a copyright judgement that is not an agent's to make. The
repository is currently **private**, which is the safe state while this is open.

If it goes public before the question is resolved, the options are: confirm the
papers are redistributable and leave them; replace them with citations and record
the substitution as a new dated frozen entry, since editing a registered one is
forbidden; or keep the repository private. Recorded in `DECISIONS.md`.

## Scrubbing — 2026-08-11

`deference-note-dump-2026-06-27/` was scrubbed under the scrubbing rules in
`AGENTS.md` before the maintainer's read-through. Round 1 made two cuts (candid assessment of a named person). Round 2, on the
maintainer's read, reversed two round-1 judgment calls and widened the scrub to
self and career material: non-consenting third parties, bio and credential
recitals, funding and mentorship-management and morale passages. All cuts are
marked inline as `[scrubbed]` with no category label, and the tree digest was
recomputed in the same change.
`SCRUB_REPORT.md` at the repository root lists every judgment call, including the
ones decided in favour of keeping.

`dose-response-note-dump-2026-07-02/` needed no cuts.

**The maintainer's read-through has not happened.** The scrub is the first pass,
not the release gate; see `DECISIONS.md`.

## Reading the digests

`sha256_tree` is over relative paths and file digests in sorted order, excluding
bytecode artifacts and `.DS_Store`. It is what CI recomputes, and it is
reproducible from the recipe in the JSON manifest's note field.

`sha256_archive` is the digest of the archive each tree was extracted from,
recorded as provenance. The archives themselves are **not kept**: frozen content
is here to be read and cited, and a zip is neither.

`consolidation_aug9/` additionally carries its own internal digest manifest over
its vendored inputs, which its own runner verifies — so the foundations-
verification gate checks a second, independent layer of digests inside the first.

## Registering something new

Extract it here, add a row above and an entry to the JSON, and say in the row
what cites it. **Do not modify an entry that is already registered.** A frozen
input that needed changing was not frozen; the honest move is a new dated entry
beside the old one.
