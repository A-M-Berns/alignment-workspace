import Cleanroom.Bli.BliMeasure.Base

/-!
# `bli-measure` · Lic: is B3 a logical inductor? (target 7, OPEN with its obstructions)

`pcB3_isLogicalInductor_open` states `IsLogicalInductor (pcB3History …) (bliDP DP states actual)`
over the recursion of record, and `paperB3_isLogicalInductor_open` over `paperDP 𝗜𝚺₁`; both are
**OPEN** (`sorry`, listed in `run/wp/bli-measure/bli-measure-open.txt`). The obstructions, as
separate named statements:

* **(i) The base's computability** — `ObstructionBaseComputable DP ov := ComputableMarket
  (pcHistory DP ov smallSet)` is open upstream (`bli-coherent-mm` F4, Known issue 8); it is
  **not** restated as a `sorry` here (never discharged, never duplicated). Nothing transfers to
  `𝐏` from a base that is not known to be a logical inductor.
* **(i′) B3's own noncomputability** (a finding of this package, F5): even over a computable base,
  `b3History` is built from two classical choices — `remainderRound` (`Classical.choose` of a
  rounding) and `faceAverage` (the uniform average of `Classical.choose`d balance solutions) — so
  `ComputableMarket (b3History base 𝓜)` (an extensional predicate on the *values* of `𝐏`) is
  **not established and not refuted; the definition gives no computable presentation** (two
  classical choices) — open in a stronger sense than (i). (This is a statement of what the
  package has, not an independence claim — audit r2 fidelity N9.) `ObstructionB3Computable` names the
  statement; a computable B3 would need a computable largest-remainder rounding and a computable
  full-support face solution (both exist mathematically; neither is built here).
* **(ii) Exact small agreement fails on the past state atoms, on every mesh** — `bli-transfer`'s
  L1 needs `E1x (ratHistory Q) 𝐏`, and B3 has it only on the **state-free** part of `smallSet n`,
  and there only on the denominator mesh (`b3_E1x_denom_stateFree`; off it a rounding error,
  `b3_E1r_err`). On a past candidate's state atom B3 prices the realized state at `1` while the
  base of record does not: `ObstructionE1x` names the exact-agreement requirement and
  `paper_obstructionE1x_refuted` (`Refuted.lean`) refutes it on the denominator mesh itself — the
  N− for (ii), on the real construction (repair round 1; the coarse-mesh rounding example the
  report once described was the wrong N−, since it only shows the state-free rounding error). So
  the gap is the realized-past convention, not the mesh; the mesh adds the state-free rounding
  error, and the denominator mesh is noncomputable in the base besides.
* **(iii) `EF`-expressibility** — not attempted; the obstruction is that an `ExprMap` for B3
  would have to express the face-average kernel, i.e. `faceGen`'s filter (an existential over
  balance solutions) and the chosen witnesses, while `bli-superbelief`'s `Expr.lean` expresses
  balance solutions of a fixed form, not a classically chosen family. No Lean statement is made
  (the record is the reason, not an attempt — audit r2 fidelity N8).

Shape to follow for a future proof: `bli-assemble`'s `bliHistory_isLogicalInductor_of` (named
hypotheses `C`, `hov`); the `noExploit` half for the base is `pcOverlay_no_ec_trader_exploits`.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFinite Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliCoherentMm

variable (DP : DeductiveProcess) (ov : Overlay)

/-- **Obstruction (i)**: the base of record is a computable market — open upstream
(`bli-coherent-mm` F4); named here, never discharged.
Source: [[bli-measure-mandate]] target 7 (i); `bli-coherent-mm` Known issue 8
Kind: D
Fidelity: exact -/
def ObstructionBaseComputable : Prop := ComputableMarket (pcHistory DP ov smallSet)

variable {DP} (base : CoherentBase DP) (𝓜 : Mesh)

/-- **Obstruction (i′)**: B3 itself is a computable market — not established and not refuted: the
definition (two classical choices, `remainderRound` and `faceAverage`) gives no computable
presentation from which FAF's extensional predicate could be decided either way; a computable B3
needs computable replacements.
Source: [[bli-measure-findings]] F5
Kind: D
Fidelity: exact -/
def ObstructionB3Computable : Prop := ComputableMarket (b3History base 𝓜)

/-- **Obstruction (ii)**: exact small agreement with the base, which `bli-transfer`'s L1 needs and
B3 has only on the state-free part of `smallSet n`, and there only on the denominator mesh
(`b3_E1x_denom_stateFree`; off it `b3_E1r_err`); on past state atoms it fails on every mesh
(`paper_obstructionE1x_refuted`, `Refuted.lean`).
Source: [[bli-measure-mandate]] target 7 (ii)
Kind: D
Fidelity: exact -/
def ObstructionE1x : Prop := E1x (Cleanroom.Bli.BliTrajectory.ratHistory base.Q) (b3History base 𝓜)

variable (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

/-- **OPEN — B3 of record is a logical inductor over its state-learning process.** Obstructions
(i)–(iii) in the module docstring; the base's own LIC is open upstream and B3 is noncomputable as
defined.
Source: [[bli-measure-mandate]] target 7
Kind: OPEN
Fidelity: exact
Hyps: (a) `hcons`, `hDP` -/
theorem pcB3_isLogicalInductor_open (hDP : ComputableDeductiveProcess DP) (𝓜 : Mesh) :
    IsLogicalInductor (pcB3History DP ov hcons 𝓜)
      (bliDP DP (wstates (recBase DP ov hcons).𝔅 𝓜) (b3Actual (recBase DP ov hcons) 𝓜)) := by
  sorry

/-- **OPEN — B3 over the paper process is a logical inductor** (instance of
`pcB3_isLogicalInductor_open`; `paperDP 𝗜𝚺₁` is computable in FAF, but the obstructions are the
same).
Source: [[bli-measure-mandate]] target 7
Kind: OPEN
Fidelity: exact
Hyps: (a) `hDP` (FAF's computability of the paper process, taken as a hypothesis here) -/
theorem paperB3_isLogicalInductor_open (hDP : ComputableDeductiveProcess (paperDP 𝗜𝚺₁)) (𝓜 : Mesh) :
    IsLogicalInductor (paperB3History ov 𝓜)
      (bliDP (paperDP 𝗜𝚺₁) (wstates (recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons).𝔅 𝓜)
        (b3Actual (recBase (paperDP 𝗜𝚺₁) ov paperDP_hcons) 𝓜)) :=
  pcB3_isLogicalInductor_open ov paperDP_hcons hDP 𝓜

end Cleanroom.Bli.BliMeasure
