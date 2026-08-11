# Frozen inputs

Immutable. Everything here is read-only, checksummed in
`FROZEN_INPUT_CHECKSUMS.json`, and referenced by path — never edited, and never
unpacked into `projects/`. A round that needs a frozen result cites it by claim
identifier against the tree named below.

| name | date | sha256 | description | cited by |
|---|---|---|---|---|
| `consolidation_aug9/` | 2026-08-09, corrections folded in 2026-08-10 | `a2ca95ad9d6cafcaecb77b7b4d7a0d75f9a33738e3ecb65437b50a56eb7a164a` (tree digest over 59 files) | The August 9 consolidation of the leverage line: six theory parts numbered 7–12, a ledger of 180 claims, and its own vendored and digest-frozen inputs. Verifies standalone with `python3 tests/run.py`. | `projects/leverage/` — the authoritative record for that line; the workspace's `CONSOLIDATION_REF.md` pins it |
| `deference-note-dump-2026-06-27.zip` | 2026-06-27 | `bc51a91b84241128380286b1a8f052a5dde01a90876dc6359cf9b6e3c9aef362` (50 files) | Note dump for the deference/corrigibility line, including the Lean development and its statement-level audit. | `projects/delegation/` — the arc it records is the delegation line's starting point |
| `dose-response-note-dump-2026-07-02.zip` | 2026-07-02 | `a69f8a9876b24dd0a2cd0b609e294c53fef0b2596c79f0037812a6a47a60e890` (13 files) | Note dump on dose-response structure in the deference setting. | `projects/delegation/` |

## Tree digests

For an unpacked tree the recorded digest is over the relative path and content
digest of every file, in sorted order, excluding bytecode artifacts. It is
reproducible: the recipe is stated in the JSON manifest's note field, and
`consolidation_aug9/` additionally carries its own internal digest manifest,
which its runner verifies.

## Registering something new

Copy the archive here, add a row above and an entry to the JSON, and say in the
row what cites it. Do not modify an entry that is already registered: a frozen
input that needed changing was not frozen, and the honest move is a new dated
entry beside the old one.
