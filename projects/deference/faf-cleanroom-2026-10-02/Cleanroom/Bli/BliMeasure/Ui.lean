import Cleanroom.Bli.BliMeasure.Base
import Cleanroom.Bli.BliRvcUi.Ui.Finite
import Cleanroom.Bli.BliRvcUi.Hm.Paper

/-!
# `bli-measure` · Ui: exact universal instantiation and hypothetical marginalization over B3
(target 8)

From target 1's coherence relative to the stage: a `UIFamily` whose instance implications lie in
the base's day-`n` stage is exactly instantiated by `𝐏_n` (`b3_UIAt`, via `bli-rvc-ui`'s
`uiAt_of_coherentOn`); over the paper process, every HM sentence is priced at its truth value
from its entry day on (`paperB3_hm_exact`, via `hm_exact_of_coherentOn`). The two-sided form
(`UITwoSided`) is **not** stated (refuted by `bli-rvc-ui`; [[plan]] risk M6). The N+ with a strict
instance over `paperDP 𝗜𝚺₁ ∪ AxProcess F` is **not done** (it needs the union process's
consistency and tag-freeness, not established here); the hypothesis package of `b3_UIAt` is
inhabited by any process containing the implications.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFinite Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliCoherentMm Cleanroom.Bli.BliRvcUi

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-- **Exact UI at a finite day over B3**: a `UIFamily` whose instance implications for `C` lie in
the base's day-`n` stage is exactly instantiated by `𝐏_n` (`𝐏_n(u) ≤ 𝐏_n(inst c)`).
Source: [[bli-measure-mandate]] target 8; [[bli-program-desiderata]] P8; `bli-rvc-ui` T3.4
Kind: C
Fidelity: stronger: implications anywhere in `DP.D n`, not only in `smallSet n ∩ DP.D n`
Hyps: (a) `hfree`, `hD` -/
theorem b3_UIAt (hfree : TagFreeProcess stateTag DP) (n : ℕ) (F : UIFamily) (C : Finset ℕ)
    (hD : ∀ c ∈ C, F.u 🡒 F.inst c ∈ DP.D n) : UIAt (b3History base 𝓜 n) F C :=
  uiAt_of_coherentOn
    (b3History_coherentOn base 𝓜 hfree n
      (sentenceAtomCodes F.u ∪ C.biUnion fun c => sentenceAtomCodes (F.inst c)))
    (fun c hc => by
      show F.u 🡒 F.inst c ∈ DP.D n ∪ stateLits base 𝓜 n
      exact Finset.mem_union_left _ (hD c hc))
    Finset.subset_union_left
    (fun c hc => (Finset.subset_biUnion_of_mem (fun c => sentenceAtomCodes (F.inst c)) hc).trans
      Finset.subset_union_right)

open Classical in
/-- **Exact HM over the paper process**: every HM sentence is priced by B3 at its truth value from
its entry day on.
Source: [[bli-measure-mandate]] target 8; `bli-rvc-ui` T4.3 (`hm_exact_of_coherentOn`)
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_hm_exact (ov : Overlay) (𝓜 : Mesh) {F : ℕ → Prop}
    (hF : ComputablePred F) (q : ℕ) :
    ∃ k, ∀ n ≥ k,
      paperB3History ov 𝓜 n (hmSentence 𝗜𝚺₁ hF q) = if F q then 1 else 0 := by
  obtain ⟨k, hk⟩ := hm_exact_of_coherentOn (T := 𝗜𝚺₁) hF q
  refine ⟨k, fun n hn => hk n hn (sentenceAtomCodes (hmSentence 𝗜𝚺₁ hF q)) _ ?_ (Finset.Subset.refl _)⟩
  exact coherentOn_mono_stage Finset.subset_union_left (paperB3_coherentOn ov 𝓜 n _)

/-- **`HMExact` over the paper process** on any finite set of codes, from some day on.
Source: [[bli-measure-mandate]] target 8 (`HMExact (b3History n) hF Q`); `bli-rvc-ui` T4.3
Kind: C
Fidelity: exact; conditional on `bli-coherent-mm`: computability open
Hyps: (a) none -/
theorem paperB3_hmExact (ov : Overlay) (𝓜 : Mesh) {F : ℕ → Prop} (hF : ComputablePred F)
    (Q : Finset ℕ) : ∃ k, ∀ n ≥ k, HMExact 𝗜𝚺₁ (paperB3History ov 𝓜 n) hF Q := by
  obtain ⟨k, hk⟩ := hmExact_of_coherentOn (T := 𝗜𝚺₁) hF Q
  refine ⟨k, fun n hn => hk n hn (Q.biUnion fun q => sentenceAtomCodes (hmSentence 𝗜𝚺₁ hF q)) _ ?_
    (fun q hq => Finset.subset_biUnion_of_mem (fun q => sentenceAtomCodes (hmSentence 𝗜𝚺₁ hF q)) hq)⟩
  exact coherentOn_mono_stage Finset.subset_union_left (paperB3_coherentOn ov 𝓜 n _)

end Cleanroom.Bli.BliMeasure
