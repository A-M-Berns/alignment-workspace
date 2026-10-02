import Cleanroom.Bli.BliWitnessLia.Prior
import Cleanroom.Bli.BliWitnessLia.Verdict
import Cleanroom.Bli.BliWitnessLia.Check
import Cleanroom.Bli.BliWitnessLia.Realized
import Cleanroom.Bli.BliWitnessLia.Checks
import Cleanroom.Bli.BliWitnessLia.Horizon2

/-!
# `bli-witness-lia` — End to end over FAF's inductor: the SIST mugging on a segment of the linked
splice, every predicate checked

Root module of the work package `bli-witness-lia` (U15/U16 of [[bli-program]] §3.9, §4). Imports
every module of the package:

- `Prior` (T1): `segmentSist`, the SIST mugging prior `sistSkel` at `bli-exact-base`'s
  `segmentSkeleton` with base table the linked splice's realized day-`n` table and coin
  `freshCoord`; the branch masses `1/2`, `1/2` derived from the inductor's kernel law.
- `Verdict` (T2): the verdict `(V − c)/2`, one-step pays, updateful refuses, `¬ ClassInert`,
  `H_unif`, faith, `NDPOL`, the source numbers (`45`).
- `Check` (T3): the §2.6 predicate check at the FAF level, tied to the prior; the refuted
  neighbours (`D_PC_on`, `D_ND_on`, `NonDegenerate`).
- `Realized` (T4): the inductor's realized next table is uncharged; the cell-form chain is what is
  charged.
- `Checks` (T5): `¬ NoCrossBranch`, `Reflective`, the auditor's contrast, the days of record.
- `Horizon2` (T9, extension): U15 at horizon two — the two-step `trajLaw` masses (two-point law, then the
  tent, which is a point mass at the decided coin), classes `1/2`, `1/2`, `0`, verdict `(V − c)/2`.

The sentence a reader may say afterwards is in [[bli-witness-lia-report]] § State. The two OPEN
rows of the dependency that bound this package — `Segment.linked_segment_day_exists` (whether a
segment day is pinned before `H`) and `Skel.segmentBli_isLogicalInductor` (the skeleton BLI's own
criterion) — are cited in docstrings and never used: nothing here rests on an OPEN statement.
-/
