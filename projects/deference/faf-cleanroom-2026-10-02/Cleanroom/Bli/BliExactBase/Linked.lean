import Cleanroom.Bli.BliExactBase.QuoteLane
import Cleanroom.Bli.BliLinkage.Determination

/-!
# `bli-exact-base` — K7d, first lemma: faith at `⊤` charges only tables that price `⊤` at `1`

K7d's first lemma (round 0; the kernel and the package over the splice are `Kernel.lean` and
`Segment.lean`, continuation 1): **a charged candidate must be coherent at `⊤`**. If `P n` is a mixture of worlds on an algebra containing the state
sentence `σ q` and faith holds at `⊤` on `q` — `P n (⊤ ⋏ σ q) = val q ⊤ · P n (σ q)` — then
`P n (σ q) > 0` forces `val q ⊤ = 1`, because every world holds `⊤ ⋏ σ q` iff it holds `σ q`.
With `⌜⊤⌝` pinned (as it is on `segmentIndex` from `N₀` on, `pinned_eventually_splice`) and
`ValuesAtRep` (the candidate's value at `⊤` is the representative of its cell), a charged table's
`⊤`-cell must have representative `1`: product-face non-degeneracy — positive mass on every
candidate of the face, including those with `⊤` off the `1` cell — is incompatible with faith
(the finding the mandate's § 4 asks for; the product-face statement itself is not proved here).
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB

/-- A world holds `⊤ ⋏ ψ` iff it holds `ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_top_and (v : PCWorld) (ψ : Sentence) : v.Holds ((⊤ : Sentence) ⋏ ψ) ↔ v.Holds ψ := by
  rw [PCWorld.holds_and]
  exact ⟨fun h => h.2, fun h => ⟨PCWorld.holds_top v, h⟩⟩

/-- A mixture prices `⊤ ⋏ ψ` as it prices `ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixture_top_and {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ} {A : Finset ℕ}
    {p : Sentence → ℝ} (hM : IsMixture W w A p) {ψ : Sentence} (hψ : sentenceAtomCodes ψ ⊆ A) :
    p ((⊤ : Sentence) ⋏ ψ) = p ψ := by
  have hA : sentenceAtomCodes ((⊤ : Sentence) ⋏ ψ) ⊆ A := by
    rw [sentenceAtomCodes_and, sentenceAtomCodes_verum, Finset.empty_union]; exact hψ
  rw [hM.rep _ hA, hM.rep ψ hψ]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (W i).Holds ψ
  · rw [payout_of_holds h, payout_of_holds ((holds_top_and _ _).2 h)]
  · rw [payout_of_not_holds h, payout_of_not_holds (fun h' => h ((holds_top_and _ _).1 h'))]

/-- **Faith at `⊤` charges only candidates valuing `⊤` at `1`** (K7d's `charged_coherent_of_faith`
at the coordinate `⊤`). If `P n` is a world mixture on an algebra containing the state sentence of
`q`, and faith at `⊤` holds on `q`, then a charged `q` (`0 < P n (σ q)`) has `val q ⊤ = 1`.
Source: mandate § 4 ("a charged `q` with `q ⊤ ≠ 1` contradicts `P n (⊤ ⋏ σ_q) = P n σ_q`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem charged_val_top_eq_one {D : Finset Sentence} {A : Finset ℕ} {p : Sentence → ℝ}
    (hcoh : CoherentOn D A p) {σq : Sentence} (hσ : sentenceAtomCodes σq ⊆ A) {valTop : ℝ}
    (hfaith : p ((⊤ : Sentence) ⋏ σq) = valTop * p σq) (hpos : 0 < p σq) : valTop = 1 := by
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 hcoh)
  rw [mixture_top_and hM hσ] at hfaith
  have : (valTop - 1) * p σq = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hpos.ne'

/-- **Consequence for the candidate grid**: under faith at `⊤` on every candidate and
`ValuesAtRep` with `⌜⊤⌝` listed, every charged candidate's `⊤`-entry is a cell of representative
`1`. Product-face non-degeneracy (positive mass on every face candidate, including those listing
`⊤` in a cell of representative `< 1`) is therefore incompatible with the package once `⌜⊤⌝` is
pinned; the non-degeneracy of record for K7d is on the coherent carrier.
Source: mandate § 4 ("product-face `NonDegenerate` is incompatible with the package once `⌜⊤⌝` is
pinned"); bli-finite `faceGen_coherentGrid_not_prod`
Kind: C
Fidelity: exact (the incompatibility with `NonDegenerate` itself is stated in prose, not as a Lean statement over `bli-finite`'s `faceProd`)
Hyps: (a) -/
theorem charged_top_cell_rep_one {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem}
    {index : ℕ → List ℕ} {D : Finset Sentence} {A : Finset ℕ} {P : History} {n : ℕ}
    (hcoh : CoherentOn D A (P n))
    (hatoms : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (stateOf C (n + 1) q) ⊆ A)
    (hval : ValuesAtRep C S index n)
    (htop : Encodable.encode (⊤ : Sentence) ∈ index (n + 1))
    (hfaith : ∀ q ∈ S.states (n + 1),
      P n ((⊤ : Sentence) ⋏ stateOf C (n + 1) q) =
        S.val (n + 1) q ⊤ * P n (stateOf C (n + 1) q))
    {q : ℕ} (hq : q ∈ S.states (n + 1)) (hpos : 0 < P n (stateOf C (n + 1) q)) :
    ∃ r ∈ C.cells (n + 1), entryOf (Encodable.encode (⊤ : Sentence)) (tableOfCode q) = some r ∧
      C.rep (n + 1) r = 1 := by
  obtain ⟨r, hr, he, hv⟩ := hval q hq _ htop
  rw [sentenceOfCode_encode] at hv
  refine ⟨r, hr, he, ?_⟩
  have := charged_val_top_eq_one hcoh (hatoms q hq) (hfaith q hq) hpos
  rw [hv] at this
  exact_mod_cast this

end Cleanroom.Bli.BliExactBase
