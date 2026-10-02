import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Found.DpCoreTree.Nodes

/-!
# Downstream-faithful masking and the test-sequence existence question (T16(c)(d), stretch)

* `StrictlyBelow B e d` — "some `e`-node is a proper descendant of some `d`-node"
  (`calibration.md` Definition C2's "strictly below").
* `FiberPropagates B` — CA-3′'s hypothesis: if some `d`-node has an `e`-node below it, every
  `d`-node does (strong fairness implies it; `dp-fairness-reloc` discharges).
* `DFMasked` — Definition C2's downstream-faithful masking: self-models full-support at `d` and at
  every point not strictly below `d`, equal to `C` strictly below `d`.
* `testSeq_exists_open` — **OPEN**: existence of a test-sequence tremble-EDT-consistent procedure on
  every finite tree with pruned chance over `ℝ` (DY-3: Kakutani per `ε` + compactness;
  `dp-dutch-book` discharges with `fix-kakutani`). Listed in `dp-calibration-open.txt`.

CA-3′ (irreflexivity and transitivity of `StrictlyBelow` under `FiberPropagates`) and the
ping-pong N− were **not attempted** (context budget); they are recorded as such in the report.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- `e` is *strictly below* `d`: some `e`-node has a `d`-node strictly above it.
Source: `cf-workflow/phase2-notes/repair/calibration.md` Definition C2 ("'`e` strictly below `d`'
:= some `e`-node is a proper descendant of some `d`-node")
Kind: D -/
def StrictlyBelow (B : Tree Ω ι acts K) (e d : ι) : Prop :=
  ∃ q : B.DecNode, pt B q = e ∧ d ∈ ancestorPts B q

/-- CA-3′'s hypothesis: if some `d`-node has an `e`-node below it, every `d`-node has one.
Source: `calibration.md` CA-3′ ("by fiber isomorphism, *every* `d`-node has an `e`-node below
it") — the hypothesis it actually uses, isolated
Kind: D -/
def FiberPropagates (B : Tree Ω ι acts K) : Prop :=
  ∀ d e : ι, (∃ q : B.DecNode, pt B q = e ∧ d ∈ ancestorPts B q) →
    ∀ q : B.DecNode, pt B q = d → ∃ q' : B.DecNode, pt B q' = e ∧ d ∈ ancestorPts B q'

/-- **Definition C2, downstream-faithful masking (DF)**: at every queried `d` some self-model `C'`
— full-support at `d` and at every point not strictly below `d`, equal to `C` at every point
strictly below `d` — realizes `O_d` and the strict clauses hold for `s_d` under it.
Source: `cf-workflow/phase2-notes/repair/calibration.md` Definition C2; `v2-amendments.md` A52
Kind: D
Fidelity: exact (no null case: on `𝔉` no point is DF-free, CA-2′(i); off `𝔉` a point with no
realizing DF self-model is simply not DF-masked, as the letter reading) -/
def DFMasked (s : ι → State Ω K) (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) : Prop :=
  ∀ d ∈ queried B, ∃ C' : Proc ι acts K,
    (∀ a, 0 < (C' d).w a) ∧
    (∀ e, ¬ StrictlyBelow B e d → ∀ a, 0 < (C' e).w a) ∧
    (∀ e, StrictlyBelow B e d → C' e = C e) ∧
    0 < nu C' B (obs d) ∧ StrictClausesAt s obs C' B d

/-- **OPEN (T16(d), DY-3)**: on every finite tree with pruned chance, over `ℝ`, some procedure is
test-sequence tremble-EDT-consistent. Route: for fixed `ε` the strictly calibrated act values are
continuous rational functions of the procedure (their denominators `ν_{C^ε}(a ∧ O_d)` are positive
iff some chance-positive leaf satisfies `a ∧ O_d`, independently of `C`), the argmax correspondence
is upper hemicontinuous with nonempty convex values (Definition 18's tie-freedom), Kakutani gives a
fixed point `C_ε` for each `ε`, and compactness of the product of simplices gives a convergent
subsequence. Kakutani is `fix-kakutani`'s; `dp-dutch-book` discharges this row once it lands.
Source: `cf-workflow/phase2-notes/repair/dynamic.md` DY-3 ("Existence on every finite tree with
pruned chance"); mandate T16(d)
Kind: OPEN
Fidelity: exact (statement over `ℝ`; the elementary convergence of `TestSeqTrembleEdtConsistent`)
Hyps: (a) every chance weight positive (pruned) -/
theorem testSeq_exists_open [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω)
    (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℝ)
    (_hpruned : ∀ ℓ, 0 < chanceWeight B ℓ) :
    ∃ C : Proc ι acts ℝ, TestSeqTrembleEdtConsistent obs actEv C B := by
  sorry

end Cleanroom.Decision.DpCalibration
