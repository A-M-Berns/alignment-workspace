import Cleanroom.Bli.BliRvcUi.Ui.Defs
import LogicalInduction.Construction.LIACompiler

/-!
# `bli-rvc-ui` · Ui/Lia: FAF's construction over the schema-augmented process is a logical inductor (T3.2)

**Soto's Step 1 in its honest form.** Soto (PDF 07, p. 1) argues that eliminating trades in
`Ax`-inconsistent worlds "will still be an LI, because if a trader exploits this market, then that
trader with trades in inconsistent worlds eliminated would also exploit it" — a one-liner that
ignores the e.c. certificate and the cash flows of the modified trader (bli-soto-a-054's flag).
Over FAF no trade-elimination argument is needed: `AxProcess F` is a computable deductive process
(`axProcess_computable`), the union with any computable base is computable, and FAF's
`LIA_is_logical_inductor` (`thm:lia`) gives an inductor over the union whose plausible worlds all
satisfy the schema instances. Findings F-5.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional

/-- **T3.2 — the LIA over `DP ∪ AxProcess F` is a logical inductor** (FAF's construction, no
trade-elimination argument).
Source: Soto PDF 07 Step 1; bli-soto-a-054; [[bli-program-desiderata]] P8; [[bli-program-construction]] U8
Kind: C
Fidelity: exact (FAF's reading of "eliminating inconsistent worlds keeps an LI")
Hyps: (a) `hDP` (the base is computable), `hinst` (the instance family is primitive recursive) -/
theorem lia_union_ax_isLI {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (F : UIFamily) (hinst : Primrec F.inst) :
    IsLogicalInductor (liaHistory (DP.union (AxProcess F))) (DP.union (AxProcess F)) :=
  LIA_is_logical_inductor _ (union_ax_computable hDP F hinst)

end Cleanroom.Bli.BliRvcUi
