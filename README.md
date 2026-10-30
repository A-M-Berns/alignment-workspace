# derived — the plain derivation of main

The two generated files of the argument map that are not committed to the
source tree (ruling F3, 2026-10-23): `graph/derived.json`, the full derivation
(every level, status, probability, value and ranked unit), and
`graph/index.json`, the structure-only index a site renders from. Both are
written by `python3 -m checkers.graph --root .` on the plain run and carry a
`generated_hash` over their own content; `graph/versions.json` on main
records each file's derivation hash, so a derivation can be checked against the
commit it came from.

This branch is replaced on every push to main by the workflow `derived`. Do not
commit to it: the next push discards whatever is here.

Derived from main at 28f2ffcb66256d4c103917f0d02f2175184b0627.
