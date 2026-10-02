import Cleanroom.Bli.BliWitnessLia.Prior

/-!
# `bli-witness-lia` · Verdict: U5 over the inductor — the SIST verdict and the two rules (T2)

`udt-bli-sist`'s `TentSist` (the tent instance over the nine-table grid) is mirrored line by line
on `segmentSist`, the SIST mugging prior over `bli-exact-base`'s linked splice: the verdict
`EU Ask give − EU Ask refuse = (V − c)/2`, one-step UDT pays (`c < V`), the updateful rule refuses
(`0 < c`), `ClassInert {Ask} Ask` fails (`V ≠ 0`), `H_unif`, faith (the finite `E2x`), `NDPOL`, and
the source-number instance `(c, V) = (10, 100) ↦ 45`.

Every theorem here is an **instance of `udt-bli-sist`'s theorem at `segmentSkeleton`**
(`verdict_sistSkel`, `homeEU_sistSkel`, `not_classInert_sistSkel`, `hUnif_sistSkel`,
`faith_sistSkel`, `ppMass_sistSkel`), Kind C; the content is the derivation of the class masses
from the inductor's kernel in `Prior.lean` (`stateMass_ask_rec`, `classMass_ask`, `classMass_rec`,
`classMass_other`), not the arithmetic. The headlines take `hK hn h2` (and the stakes) only: no
headline takes `stateMass … = 1/2` or `askC Qh` as a hypothesis (mandate § 6).

**The residual class has mass `0`** (mandate § 3.3, § 5 item 6): the two-point law charges only
the two slice marginals, so the verdict's residual term `μ(Other)·(r₀ give − r₀ refuse)` vanishes
identically and the verdict is `(V − c)/2 = 45` at the source's numbers — unlike the tent's
`1/3, 1/3, 1/3` (`TentSist.verdict`: `30 + (r₀ give − r₀ refuse)/3`) and the source's `49/49/2`.
This is not a degeneracy of the mugging (both branches it needs are charged `1/2`,
[[bli-program]] §7 item 11); it is a difference from the source's proportions, disclosed here and
in the ledger.

Sources: [[bli-program]] §3.9 (U5, U15); bli-slides-034; mandate T2; udt-bli-sist T8
(`TentSist`, the template).
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

section Verdict

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
variable (c V : ℚ) (r₀ : Bool → ℚ)

/-- **The SIST verdict over the inductor**: at the Ask table,
`EU Ask give − EU Ask refuse = (V − c)/2`. Instance of `udt-bli-sist`'s `verdict_sistSkel` at
`segmentSkeleton` with the class masses of `Prior.lean`: `μ(Rec ∖ Ask) = 1/2`, `μ(Ask) = 1/2`,
`μ(Other) = 0` — so the residual term is `0 · (r₀ give − r₀ refuse)` and drops (the source's
`49/49/2` is not reproduced; mandate § 3.3). The content is the masses: they are the inductor's
kernel law at its realized day-`n` table (`stateMass_ask_rec`).
Source: [[bli-program]] §3.9 (U5/U15); bli-slides-034; mandate T2 (`verdict`)
Kind: C (instance of `verdict_sistSkel` at `segmentSkeleton`; the content is the masses)
Fidelity: exact (residual class of mass `0`, disclosed)
Hyps: (a) -/
theorem verdict :
    (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) true -
      (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) false = (V - c) / 2 := by
  rw [verdict_sistSkel _ _ _ _ _ _ _ _ _ (askC_askTable hK hn h2), classMass_rec hK hn h2 c V r₀,
    classMass_ask hK hn h2 c V r₀, classMass_other hK hn h2 c V r₀]
  ring

/-- **One-step UDT pays over the inductor** whenever `c < V`: `give` is the one-step choice at the
Ask table, strictly (`EU Ask refuse < EU Ask give`; `refuse` is the only other action).
Source: [[bli-program]] §3.9 (U5/U15); bli-slides-034; mandate T2 (`isOneStepChoice_pay`)
Kind: C (instance; from `verdict`)
Fidelity: exact
Hyps: (a) `c < V` -/
theorem isOneStepChoice_pay (hcV : c < V) :
    (segmentSist H K hK n hn h2 c V r₀).IsOneStepChoice (askTable K hK hn) true ∧
      (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) false <
        (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) true := by
  have hd := verdict hK hn h2 c V r₀
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

/-- **The updateful rule refuses over the inductor** whenever `0 < c`:
`homeEU Ask give = −c < 0 = homeEU Ask refuse`. Instance of `homeEU_sistSkel` at
`segmentSkeleton`, with the Ask table's positive mass derived (`stateMass_ask_pos`) and
`askC askTable` proved (`askC_askTable`), never assumed.
Source: [[bli-program]] §3.9 (U5); mandate T2 (`isUpdatefulChoice_refuse`)
Kind: C (instance of `homeEU_sistSkel`)
Fidelity: exact
Hyps: (a) `0 < c` -/
theorem isUpdatefulChoice_refuse (hc : 0 < c) :
    (segmentSist H K hK n hn h2 c V r₀).IsUpdatefulChoice (askTable K hK hn) false ∧
      ¬ (segmentSist H K hK n hn h2 c V r₀).IsUpdatefulChoice (askTable K hK hn) true := by
  have h := homeEU_sistSkel (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n (by omega))
    c V r₀ (askTable K hK hn) (askC_askTable hK hn h2) (stateMass_ask_pos hK hn h2 c V r₀)
  constructor
  · intro b
    rw [h, h]
    cases b <;> simp <;> linarith
  · intro hT
    have := hT false
    rw [h, h] at this
    simp at this
    linarith

/-- **`ClassInert {Ask} Ask` fails over the inductor** whenever `V ≠ 0`: the Rec table has mass
`1/2` and its value of the Ask point moves by `V` (`condEU_rec_sistSkel`). Instance of
`not_classInert_sistSkel`; the Rec table's positive mass is derived (`stateMass_rec_pos`).
Source: [[bli-program]] §3.9 (U5: "`NoCrossBranch` fails"); mandate T2 (`not_classInert`)
Kind: C (instance of `not_classInert_sistSkel`)
Fidelity: exact
Hyps: (a) `V ≠ 0` -/
theorem not_classInert (hV : V ≠ 0) :
    ¬ ClassInert (segmentSist H K hK n hn h2 c V r₀) {askTable K hK hn} (askTable K hK hn) :=
  not_classInert_sistSkel _ _ _ _ _ _ _ _ _ (askC_askTable hK hn h2) (recC_recTable hK hn h2)
    (not_askC_recTable hK hn h2) (stateMass_rec_pos hK hn h2 c V r₀) hV

/-- **`H_unif` holds over the inductor** at the Ask table: on every world of positive mass the
policy takes the same value at every Ask-class table as at `askTable` (the `unifLaw`
construction, `hUnif_sistSkel`).
Source: bli-soto-a-2-013; mandate T2 (`hUnif`)
Kind: C (instance of `hUnif_sistSkel`)
Fidelity: exact
Hyps: (a) -/
theorem hUnif :
    HUnif (segmentSist H K hK n hn h2 c V r₀) (askC n 0 (coinAt n (by omega))) (askTable K hK hn) :=
  hUnif_sistSkel _ _ _ _ _ _ _ _ _ (askC_askTable hK hn h2)

/-- **Faith over the inductor is derived** (`ofSkeleton_faith`, the finite `E2x`): within each
grid table's branch, the frequency of every day-`(n+1)` small sentence is the table's price.
Source: mandate T2 (`faith`); [[bli-program]] §3.9 (U15: "branch beliefs derived from `E2x`")
Kind: C (instance of `faith_sistSkel`)
Fidelity: exact
Hyps: (a) -/
theorem faith (T : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)))
    (φ : ↥(smallIndex.S (n + 0 + 1))) :
    integralOf (segmentSist H K hK n hn h2 c V r₀).μ
        (fun ω => ind ((segmentSist H K hK n hn h2 c V r₀).small ω φ))
        (fun ω => (segmentSist H K hK n hn h2 c V r₀).state ω = T) =
      T.1 φ * (segmentSist H K hK n hn h2 c V r₀).stateMass T :=
  faith_sistSkel (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n (by omega)) c V r₀
    (askTable K hK hn) T φ

/-- **Every policy point has mass `1/2`** (`NDPOL`) over the inductor (`ppMass_sistSkel`).
Source: mandate T2 (`ndpol`)
Kind: C (instance of `ppMass_sistSkel`)
Fidelity: exact
Hyps: (a) -/
theorem ndpol : (segmentSist H K hK n hn h2 c V r₀).NDPOL := fun T a => by
  rw [ppMass_sistSkel]; norm_num

/-- **The source's numbers**: at `(c, V) = (10, 100)` the verdict is `45`, for every residual `r₀`
(the residual class has mass `0`, so `|r₀| ≤ 10` is not even needed). One-step UDT pays by `45`;
the tent's instance has `30 + (r₀ give − r₀ refuse)/3`.
Source: bli-slides-034 (the numbers); mandate T2 (`instance_pay`), § 3.3
Kind: C (instance of `verdict`)
Fidelity: exact
Hyps: (a) -/
theorem instance_pay :
    (segmentSist H K hK n hn h2 10 100 r₀).EU (askTable K hK hn) true -
      (segmentSist H K hK n hn h2 10 100 r₀).EU (askTable K hK hn) false = 45 := by
  rw [verdict]; norm_num

/-- **The source's numbers, both rules**: at `(10, 100)` one-step UDT gives (strictly) and the
updateful rule refuses, over the inductor.
Source: bli-slides-034; mandate T2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem instance_rules :
    ((segmentSist H K hK n hn h2 10 100 r₀).IsOneStepChoice (askTable K hK hn) true ∧
      (segmentSist H K hK n hn h2 10 100 r₀).EU (askTable K hK hn) false <
        (segmentSist H K hK n hn h2 10 100 r₀).EU (askTable K hK hn) true) ∧
    ((segmentSist H K hK n hn h2 10 100 r₀).IsUpdatefulChoice (askTable K hK hn) false ∧
      ¬ (segmentSist H K hK n hn h2 10 100 r₀).IsUpdatefulChoice (askTable K hK hn) true) :=
  ⟨isOneStepChoice_pay hK hn h2 10 100 r₀ (by norm_num),
    isUpdatefulChoice_refuse hK hn h2 10 100 r₀ (by norm_num)⟩

end Verdict

end

end Cleanroom.Bli.BliWitnessLia
