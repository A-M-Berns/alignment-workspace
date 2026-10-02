import Cleanroom.Bli.BliAssemble.Map
import Cleanroom.Bli.BliAssemble.Coding

/-!
# `bli-assemble` · Certificate: the two instance obligations (targets 5 and 6)

`bli-transfer`'s headline of record, `overlay_isLogicalInductor'`, leaves the instance two
obligations: a `SpliceCertificate` for the expression map and a `ComputableTable` for the
re-pricing. This file states both for the tent map at the dyadic mesh and the write-out coding,
and is honest about what is proved:

* `tentExprRun` — the run-level lookup: parse the buffered run with FAF's `parseRpn` (which
  accepts every spelling — canonical, Gödel escape, structured escape), and emit the flat
  spelling `EF.rawSerialize` of the map's body for the parsed sentence. **Proved**:
  `tentRunAgrees : RunAgrees (tentExprMap 𝓜 c) (tentExprRun 𝓜 c)` — by construction, on every
  spelling `parseRpn` accepts.
* `tentOracle_exists` — **OPEN**: a polynomial-time `SpliceOracle` for `tentExprRun` at the
  dyadic mesh and the write-out coding. This is the single hard leaf of the package (mandate
  target 6 (iii)): an `FP` machine on the buffered run's bits that recognizes a Tier-A sentence,
  decodes the write-out code, computes the tent term's constants (`chainFrom` by repeated
  squaring on digit words) and the restart constant, and emits the escape-expanded raw body,
  with a polynomial output bound — plausible by `tentExpr_escExpand_digitize_length_le_poly`
  and `writeOutCode_card_le_log`, not proved. Stated as `Nonempty (SpliceOracle …)` so that the
  statement is a proposition and the certificate below is built from it by choice.
* `tentCertificate` — the certificate, resting on the open oracle (listed in
  `bli-assemble-open.txt` for that reason).
* `bliOv_computableTable` — **OPEN** (target 5): the re-pricing at the dyadic mesh and the
  write-out coding is a computable table given the base's. The mathematics is finite rational
  arithmetic over an enumerable grid; the Lean obstacles are that `smallSet`, `grid` and hence
  `chainProbH` are `noncomputable` (`Finset`s of a noncomputable carrier — `bli-found`'s unlanded
  `smallList`), so a `Computable` proof must re-implement the table over lists and prove it
  equal. Not attempted beyond the statement; the headline of record carries `hov` as a named
  hypothesis instead.

Nothing here is quantified over traders (mandate trap (ii) of `bli-transfer`).

Sources: [[bli-program]] §3.1 (iii), §3.4; mandate targets 5, 6.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## The run-level lookup and its agreement with the map (target 6 (i)–(ii)) -/

/-- **The run-level lookup**: parse the buffered run as a sentence (FAF's `parseRpn`, every
accepted spelling) and return the flat spelling of the map's body at the day `D`, or nothing.
Source: mandate target 6 (i)
Kind: D
Fidelity: n/a -/
def tentExprRun (𝓜 : Mesh) (c : StateCoding 𝓜) (b : List ℕ) (D : ℕ) : Option (List ℕ) :=
  match parseRpn b.length b with
  | some (φ, []) => (tentExprMap 𝓜 c D φ).map EF.rawSerialize
  | _ => none

/-- **The lookup agrees with the map on every spelling `parseRpn` accepts** (target 6 (ii)): by
construction, since the lookup parses with `parseRpn` itself.
Source: mandate target 6 (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tentRunAgrees (𝓜 : Mesh) (c : StateCoding 𝓜) :
    RunAgrees (tentExprMap 𝓜 c) (tentExprRun 𝓜 c) := by
  intro b φ hb D
  unfold tentExprRun
  rw [hb]

/-! ## The oracle (target 6 (iii)) — OPEN -/

/-- **OPEN — the polynomial-time oracle for the tent lookup** at the dyadic mesh and the write-out
coding: an `FP` function of the packed word `pair zW (pair tokW bufW)` whose decoded output is
`tentExprRun … (decodeBits bufW) (digitVal cur) ++ [8]` (or nothing), block-well-formed, with a
polynomial output bound. The plausibility argument (not a proof): the input carries the state
atom's digits, of which there are at least `|S m|` by `writeOutCode_card_le_log`; the output is
the escape-expanded tent term, of `O(|S m| · (K + 1))` digits by
`tentExpr_escExpand_digitize_length_le_poly`, plus one rational constant whose numerator and
denominator are bounded by `chainDen_le_pow`-type bounds at a mesh `d m = 2^m` with
`m ≤ log log input`; the arithmetic is FAF's `DigitFP` kit. Nothing of this is formalized here.
Source: mandate target 6 (iii) ("if (iii) resists, isolate the single leaf")
Kind: OPEN
Fidelity: n/a -/
theorem tentOracle_exists :
    Nonempty (SpliceOracle (tentExprRun dyadicMesh (writeOutCoding dyadicMesh))) := by
  sorry

/-- **The splice certificate for the tent map** at the dyadic mesh and the write-out coding:
the lookup, its (proved) agreement with the map, and the (open) oracle. Rests on
`tentOracle_exists`; listed as open for that reason.
Source: mandate target 6
Kind: OPEN
Fidelity: n/a (rests on the open oracle) -/
def tentCertificate :
    SpliceCertificate (tentExprMap dyadicMesh (writeOutCoding dyadicMesh)) where
  exprRun := tentExprRun dyadicMesh (writeOutCoding dyadicMesh)
  agrees := tentRunAgrees dyadicMesh (writeOutCoding dyadicMesh)
  oracle := Classical.choice tentOracle_exists

/-! ## The re-pricing as a computable table (target 5) — OPEN -/

/-- **OPEN — the re-pricing is a computable table** at the dyadic mesh and the write-out coding,
given the base's table: Mathlib `Computable` (partial recursive), not `FP`. The content is
finite rational arithmetic — parse the Gödel code (`bli-transfer`'s `tsCode`/`smallCode` kit),
enumerate the day's small sentences, decode the write-out code, run `chainProbH` over the
enumerated grid. Not attempted: `smallSet`, `grid` and `chainProbH` are `noncomputable` in
Lean, so the proof must re-implement the table over a computable enumeration (`bli-found`'s
unlanded `smallList`, with the converse size bound `encode φ ≤ g (tokenSize φ)`) and prove the
re-implementation equal to `bliOv`.
Source: mandate target 5
Kind: OPEN
Fidelity: n/a -/
theorem bliOv_computableTable (Q : RatHistory) (hQ : ComputableTable Q) :
    ComputableTable
      (bliOv Q dyadicMesh (tentSkeleton smallIndex dyadicMesh) (writeOutCoding dyadicMesh)) := by
  sorry

end

end Cleanroom.Bli.BliAssemble
