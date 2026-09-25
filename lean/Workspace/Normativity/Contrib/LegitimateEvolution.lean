/-
# Deprecated names: `LegitimateEvolution`

The declarations of this namespace moved to `OpenIntegrityEvolution` when legitimacy was
broadened to internal ∧ external (`projects/deference/rounds/2026-09-25-legitimacy-internal-external/`).
The conjunction "Integrity evolution robustly open at every state" is now the **open
Integrity evolution**, one component of legitimacy and not legitimacy itself.  These
aliases keep the old registered names resolving for one release; every current statement
uses the new names.
-/
import Workspace.Normativity.Contrib.OpenIntegrityEvolution

namespace Workspace.Normativity.Contrib.LegitimateEvolution

open Workspace.Normativity.Contrib.OpenIntegrityEvolution

@[deprecated OpenIntegrityEvolution.ObligationState (since := "2026-09-25")]
abbrev ObligationState := @OpenIntegrityEvolution.ObligationState

@[deprecated OpenIntegrityEvolution.Evolution (since := "2026-09-25")]
abbrev Evolution := @OpenIntegrityEvolution.Evolution

@[deprecated OpenIntegrityEvolution.Evolution.conservation (since := "2026-09-25")]
alias Evolution.conservation := OpenIntegrityEvolution.Evolution.conservation

@[deprecated OpenIntegrityEvolution.Evolution.propagate_toSegment (since := "2026-09-25")]
alias Evolution.propagate_toSegment := OpenIntegrityEvolution.Evolution.propagate_toSegment

@[deprecated OpenIntegrityEvolution.OpenIntegritySegment (since := "2026-09-25")]
abbrev LegitimateSegment := @OpenIntegrityEvolution.OpenIntegritySegment

@[deprecated OpenIntegrityEvolution.OpenIntegritySegment.trans (since := "2026-09-25")]
alias LegitimateSegment.trans := OpenIntegrityEvolution.OpenIntegritySegment.trans

@[deprecated OpenIntegrityEvolution.OpenIntegritySegment.answerable (since := "2026-09-25")]
alias LegitimateSegment.answerable := OpenIntegrityEvolution.OpenIntegritySegment.answerable

@[deprecated OpenIntegrityEvolution.OpenIntegrity (since := "2026-09-25")]
abbrev Legitimate := @OpenIntegrityEvolution.OpenIntegrity

@[deprecated OpenIntegrityEvolution.OpenIntegrity.trans (since := "2026-09-25")]
alias Legitimate.trans := OpenIntegrityEvolution.OpenIntegrity.trans

namespace Witness

@[deprecated OpenIntegrityEvolution.Witness.endpoint_only_insufficient (since := "2026-09-25")]
alias endpoint_only_insufficient := OpenIntegrityEvolution.Witness.endpoint_only_insufficient

end Witness

end Workspace.Normativity.Contrib.LegitimateEvolution

set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.conservation
set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Evolution.propagate_toSegment
set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.trans
set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.LegitimateSegment.answerable
set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Legitimate.trans
set_option linter.deprecated false in
#print axioms Workspace.Normativity.Contrib.LegitimateEvolution.Witness.endpoint_only_insufficient
