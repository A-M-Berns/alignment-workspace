import Cleanroom.Corrigibility.CorrScimCid.DSep

/-!
# Audit r2 (adversarial) probe: LB4 does not hold on the package's graph of record

`DSep.dsep_with_link` (LB4, `H ⊥ U ∣ {L, O}`) is proved on the paper's exact Fig. 1 graph plus the
information link (`DSep.G₂`). The Theorem 14 / Prop. 15 / entrenching-agent witnesses live on a
different graph, the graph of record `Fig1.G`, which adds `M → U` and `H → U` so that Lemma 22/23's
`g^U` can read `Pa_H` and `S` in the class of record. With `H → U` an edge, `H` is a parent of `U`
and no conditioning set d-separates them: the LB4 fact is false on the graph of record plus the
link. So the package's "Fig. 1" is two graphs, and the FUD-as-d-separation fact and the Thm 14 ⇐
hypothesis package are not simultaneously available on one of them. (This is the paper's own
tension: Lemma 23's `g^U` reads `H`, i.e. the proof of Thm 14 enlarges `Pa_U` by `H`.)
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.AuditR2

open FactoredSpaces Fig1.Node

/-- The graph of record (`Fig1.G`: the paper's edges plus `M → U`, `H → U`) with `L → O` added. -/
def adjR : Fig1.Node → Fig1.Node → Bool
  | L, O => true
  | u, v => Fig1.adjB u v

/-- The graph of record with the information link. -/
def GR : Digraph Fig1.Node := ⟨fun u v => adjR u v = true⟩

instance : DecidableRel GR.Adj := fun u v => inferInstanceAs (Decidable (adjR u v = true))

lemma GR_acyclic : GR.IsAcyclic := Digraph.isAcyclic_of_rank Fig1.rank (by decide)

/-- `H → U` is an edge of the graph of record, with or without the link. -/
theorem record_graph_has_H_U : Fig1.G.Adj H U ∧ GR.Adj H U := by decide

/-- `GR` contains `G₂` (the paper's graph plus the link): every edge of `G₂` is an edge of `GR`. -/
theorem G₂_le_GR : ∀ u v, DSep.G₂.Adj u v → GR.Adj u v := by decide

/-- On the graph of record plus the link, `H` and `U` are **not** d-separated given `{L, O}`:
`H` itself is an unblocked ancestor of both (`H → U`, `H ∉ {L, O}`). -/
theorem not_dsep_record_with_link : ¬ GR.DSeparated {H} {U} {L, O} :=
  not_dSeparated_of_common_unblocked GR_acyclic (x := H) (Finset.mem_singleton_self H)
    (Finset.mem_singleton_self U) (by decide) (by decide)
    ((Digraph.mem_unblockedAnc_iff).mpr Relation.ReflTransGen.refl)
    ((Digraph.mem_unblockedAnc_iff).mpr (Relation.ReflTransGen.single ⟨by decide, by decide⟩))

/-- For contrast, the package's LB4 on the paper's graph plus the link. -/
theorem lb4_on_paper_graph : DSep.G₂.DSeparated {H} {U} {L, O} := DSep.dsep_with_link

end Cleanroom.Corrigibility.CorrScimCid.AuditR2
