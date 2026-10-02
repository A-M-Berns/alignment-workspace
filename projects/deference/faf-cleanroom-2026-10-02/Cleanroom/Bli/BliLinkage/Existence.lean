import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkageB.Existence

/-!
# `bli-linkage` — K5a/b: B2 existence, the product coupling of record (of record)

Only **attempt B** built K5a/b (`BliLinkageB.ProductLaw`, `Existence`); attempt A did not start
them. Restated here over the record definitions:

* the abstract finite iff (`exists_coupling_iff`, over function-tables `Fin k → Fin d`): a law
  with prescribed marginals `w` and balances `b` exists iff every `w i` is a probability vector
  and `b i = ∑_r rep r · w i r` — at the package level the right side is `D_NNUcell` on the
  pinned coordinates;
* the **product coupling of record** on the package's coded tables
  (`exists_superbelief_of_d_nnucell`): probability-vector literal prices on the pinned block and
  `D_NNUcell` give a nonnegative mass-one superbelief with the base's cell masses (β) and
  balance (α) on every pinned coordinate, the unpinned block's law a parameter;
* the (⇒) on tables (`d_nnucell_at_of_feasible`); K5b's support fact (every feasible law lives
  inside `supp⊗`) and positivity of the product coupling on all of `supp⊗`;
* the N+ (four tables all charged `1/4`, marginals `1/2`, hypotheses inhabited by a constant
  base — disclosed).

Stated for a superbelief `μ` on tables (the mandate's K5a), not for a world-mixture `P` on the
whole algebra; the package-level (⇒) through a coherent `P` is `Determination.determination`.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB.Existence

/-- **K5a, the abstract finite iff (of record).** Over function-tables `Fin k → Fin d`: a law
with marginals `w` and balances `b` (at representatives `rep`) exists iff every `w i` is a
probability vector and `b i = ∑_r rep r · w i r`. (⇐) is the product coupling `productLaw w`.
Source: [[bli-program]] §3.6(v); bli-soto-b-044; bli-slides-010/011 (FB-9); mandate K5a; attempt B `Existence.exists_coupling_iff`
Kind: P
Fidelity: exact (abstract: function-tables; the pinned/unpinned split is the choice of `w`)
Hyps: (a) -/
theorem exists_coupling_iff {k d : ℕ} (w : Fin k → Fin d → ℝ) (rep : Fin d → ℝ) (b : Fin k → ℝ) :
    (∃ μ : (Fin k → Fin d) → ℝ, (∀ f, 0 ≤ μ f) ∧ ∑ f, μ f = 1 ∧
        (∀ i r, ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i = r), μ f = w i r) ∧
        (∀ i, ∑ f, μ f * rep (f i) = b i)) ↔
      (∀ i r, 0 ≤ w i r) ∧ (∀ i, ∑ r, w i r = 1) ∧ (∀ i, b i = ∑ r, rep r * w i r) :=
  Cleanroom.Bli.BliLinkageB.Existence.exists_coupling_iff w rep b

/-- **K5b, support**: a nonnegative law with marginals `w` vanishes on every table some entry of
which has zero marginal mass — every feasible `μ` lives inside `supp⊗`.
Source: mandate K5b; attempt B `Existence.support_of_feasible`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem support_of_feasible {k d : ℕ} {μ : (Fin k → Fin d) → ℝ} (hμ0 : ∀ f, 0 ≤ μ f)
    {w : Fin k → Fin d → ℝ}
    (hmarg : ∀ i r, ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i = r), μ f = w i r)
    {f : Fin k → Fin d} (hf : μ f ≠ 0) : ∀ i, 0 < w i (f i) :=
  Cleanroom.Bli.BliLinkageB.Existence.support_of_feasible hμ0 hmarg hf

/-- **K5b, positivity**: the product coupling is positive on all of `supp⊗` — the face theorem on
the constrained polytope, stated directly.
Source: mandate K5b; attempt B `Existence.productLaw_pos`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem productLaw_pos {k d : ℕ} {w : Fin k → Fin d → ℝ} {f : Fin k → Fin d}
    (hw : ∀ i, 0 < w i (f i)) : 0 < productLaw w f :=
  Cleanroom.Bli.BliLinkageB.Existence.productLaw_pos hw

/-- **K5a (⇒) on the coded tables**: a superbelief on `tables cs d` with the base's marginals (β)
and balance (α) at a coordinate forces the `D_NNUcell` identity there.
Source: mandate K5a ("(⇒) is K2(c)"); attempt B `Existence.d_nnucell_at_of_feasible`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem d_nnucell_at_of_feasible {d : ℕ} {cs : List ℕ} (hnd : cs.Nodup) (μ : ℕ → ℝ)
    (hμ : ∀ q ∉ tables cs d, μ q = 0) (rep : ℕ → ℝ) {i : ℕ} (hi : i < cs.length) (w : ℕ → ℝ)
    (b : ℝ) (hmarg : ∀ r < d, cellMassOf (tables cs d) μ (cs[i]'hi) r = w r)
    (hbal : ∑ q ∈ tables cs d, μ q * valOf rep q (cs[i]'hi) = b) :
    b = ∑ r ∈ Finset.range d, rep r * w r :=
  Cleanroom.Bli.BliLinkageB.Existence.d_nnucell_at_of_feasible hnd μ hμ rep hi w b hmarg hbal

/-- **K5a (⇐), the product coupling of record on the package's coded tables.** On day `n`, over
a family with cells `range d` and a duplicate-free index, if the base's literal prices form a
probability vector on every pinned coordinate (`hprob`) and `D_NNUcell C index Q` holds, then for
any balanced laws `ν` on the unpinned coordinates there is a nonnegative superbelief `μ` on
`tables (index (n+1)) d` of total mass `1` with (β) `cellMassOf … μ c r = Q n (lit_{n+1,c,r})` and
(α) `∑_q μ q · valOf rep q c = Q n φ_c` on every pinned `c`: `μ = lawOnCodes (productLaw w)`,
`w` the literal prices on the pinned block and `ν` elsewhere.
Source: [[bli-program]] §3.6(v); construction C6; bli-slides-010/011; mandate K5a (judged item 5); attempt B `Existence.exists_superbelief_of_d_nnucell`
Kind: C
Fidelity: exact (the unpinned block's law a parameter; cells `range d`; duplicate-free index; a superbelief on tables, not a world mixture)
Hyps: (a) -/
theorem exists_superbelief_of_d_nnucell {d : ℕ} {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲)
    (index : ℕ → List ℕ) (Q : History) (n : ℕ) (hnd : (index (n + 1)).Nodup)
    (hcells : C.cells (n + 1) = Finset.range d)
    (hprob : ∀ c ∈ pinned C index n,
      (∀ r < d, 0 ≤ Q n (C.literal (n + 1) (sentenceOfCode c) r)) ∧
        ∑ r ∈ Finset.range d, Q n (C.literal (n + 1) (sentenceOfCode c) r) = 1)
    (hdnnu : D_NNUcell C index Q) (ν : ℕ → ℕ → ℝ)
    (hν : ∀ c, (∀ r < d, 0 ≤ ν c r) ∧ ∑ r ∈ Finset.range d, ν c r = 1) :
    ∃ μ : ℕ → ℝ, (∀ q, 0 ≤ μ q) ∧ ∑ q ∈ tables (index (n + 1)) d, μ q = 1 ∧
      (∀ c ∈ pinned C index n, ∀ r < d,
        cellMassOf (tables (index (n + 1)) d) μ c r = Q n (C.literal (n + 1) (sentenceOfCode c) r)) ∧
      (∀ c ∈ pinned C index n,
        ∑ q ∈ tables (index (n + 1)) d, μ q * valOf (fun r => (C.rep (n + 1) r : ℝ)) q c =
          Q n (sentenceOfCode c)) :=
  Cleanroom.Bli.BliLinkageB.Existence.exists_superbelief_of_d_nnucell C index Q n hnd hcells hprob
    hdnnu ν hν

/-- **N+ for K5a/b**: two distinct coordinates, two cells, uniform marginals `1/2` — the product
coupling charges all four tables `1/4` and has cell masses `1/2` on both coordinates.
Source: mandate K5b (N+); attempt B `Existence.fourTables_charged`/`fourTables_marginals`
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem fourTables (c₁ c₂ : ℕ) (hne : c₁ ≠ c₂) :
    (∀ f : Fin [c₁, c₂].length → Fin 2,
      lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)) (codeOf [c₁, c₂] f) = 1 / 4) ∧
    ∀ r < 2, cellMassOf (tables [c₁, c₂] 2) (lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)))
        c₁ r = 1 / 2 ∧
      cellMassOf (tables [c₁, c₂] 2) (lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)))
        c₂ r = 1 / 2 :=
  ⟨fun f => Cleanroom.Bli.BliLinkageB.Existence.fourTables_charged c₁ c₂ f,
    fun _ hr => Cleanroom.Bli.BliLinkageB.Existence.fourTables_marginals c₁ c₂ hne hr⟩

/-- **The hypotheses of `exists_superbelief_of_d_nnucell` are inhabited** by the constant base
`Q ≡ 1/2` at the witness family's representatives `1/4, 3/4` (`1/2 = 1/4 · 1/2 + 3/4 · 1/2`),
on any index and day. A constant market — not coherent, not an inductor; the theorem reads one
day's data (disclosed). Graded N+ with the note (audit r1 fidelity N3): the inhabited theorem is
a one-day statement, so constancy in `n` and in the sentence is immaterial to what it exercises
— the uncertain values `1/2`, `1/2` at the two cells are the content, and `fourTables` carries
the four-table product coupling.
Source: mandate K5a (N+); attempt B `Existence.halfBase_hypotheses`
Kind: N+
Fidelity: n/a (constant base, disclosed; one-day theorem, constancy immaterial)
Hyps: (a) -/
theorem halfBase_hypotheses (index : ℕ → List ℕ) (n : ℕ) :
    (∀ c ∈ pinned Cleanroom.Bli.BliLinkageB.Witness.wCF index n,
      (∀ r < 2, (0 : ℝ) ≤ (fun _ _ => (1 / 2 : ℝ) : History) n
        (Cleanroom.Bli.BliLinkageB.Witness.wCF.literal (n + 1) (sentenceOfCode c) r)) ∧
        ∑ r ∈ Finset.range 2, (fun _ _ => (1 / 2 : ℝ) : History) n
          (Cleanroom.Bli.BliLinkageB.Witness.wCF.literal (n + 1) (sentenceOfCode c) r) = 1) ∧
      D_NNUcell Cleanroom.Bli.BliLinkageB.Witness.wCF index (fun _ _ => (1 / 2 : ℝ)) :=
  Cleanroom.Bli.BliLinkageB.Existence.halfBase_hypotheses index n

end Cleanroom.Bli.BliLinkage
