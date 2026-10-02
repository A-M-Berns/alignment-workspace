import Cleanroom.Bli.BliLinkageB.ProductLaw
import Cleanroom.Bli.BliLinkageB.Determination
import Cleanroom.Bli.BliLinkageB.Witness

/-!
# bli-linkage, angle B — K5a at the package's coded tables (B2 existence)

`ProductLaw.lean` works over function-tables `Fin k → Fin d`. The package's superbeliefs live on
*codes* of tables (`tableOfCode`, `entryOf`, `cellMass`), so this module transports: `codeOf cs f`
is the code of the table `cs.zip (ofFn f)` (injective; its entry at `cs[i]` is `f i` when `cs`
has no duplicates), `tables cs` is the finset of all such codes, `lawOnCodes` pushes a law on
function-tables to codes, and `cellMassOf`/`balanceOf` are `cellMass`'s and the B2 `val`'s
shapes on a superbelief `μ : ℕ → ℝ`.

**K5a (⇐), the product coupling of record** (`exists_superbelief_of_d_nnucell`): on day `n`,
over a cell family `C` with cells `Finset.range d` and a duplicate-free index, if the base's
prices of tomorrow's cell literals form a probability vector on every pinned coordinate and
`D_NNUcell C index Q` holds, then for any choice of balanced laws `ν` on the unpinned
coordinates there is a superbelief `μ` on `tables (index (n+1))` — nonnegative, total mass `1`
— whose cell masses on every pinned coordinate are the base's literal prices (β) and whose
balance at the representatives on every pinned coordinate is the base's price of the
coordinate (α). The law is `lawOnCodes (productLaw w)` with `w` the literal prices on the pinned
block and `ν` on the rest: the mandate's `productCoupling`, with the unpinned part a parameter.

**K5a (⇒)** (`d_nnucell_at_of_feasible`): any superbelief on `tables cs` with (β) at a
coordinate and (α) there forces the `D_NNUcell` identity at that coordinate — the regrouping
`balance_of_marginals`, no coupling needed; the package-level (⇒) through a coherent `P` is
`Determination.d_nnucell_of_package`.

**K5b** is in `ProductLaw.lean` (`support_of_feasible`, `productLaw_pos`). The N+ for the
coupling is the two-coordinate, two-cell instance this module ends with (`fourTables_charged`,
`fourTables_marginals`, `halfBase_hypotheses`): with the base at `1/2` on both coordinates'
literals, the product coupling charges all four tables `1/4` each and has cell masses `1/2`.
-/

namespace Cleanroom.Bli.BliLinkageB

namespace Existence

open Finset LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound

variable {d : ℕ}

/-! ## Coded tables -/

/-- **The code of a function-table**: the table listing `cs[i] ↦ f i`.
Source: mandate K5a (tables over `index (n+1)` with entries in `cells (n+1)`)
Kind: D
Fidelity: n/a -/
def codeOf (cs : List ℕ) (f : Fin cs.length → Fin d) : ℕ :=
  Encodable.encode (cs.zip (List.ofFn fun i => (f i : ℕ)))

/-- Decoding a coded function-table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableOfCode_codeOf (cs : List ℕ) (f : Fin cs.length → Fin d) :
    tableOfCode (codeOf cs f) = cs.zip (List.ofFn fun i => (f i : ℕ)) :=
  tableOfCode_encode _

/-- `codeOf cs` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma codeOf_injective (cs : List ℕ) : Function.Injective (codeOf cs : (Fin cs.length → Fin d) → ℕ) := by
  intro f g h
  have h1 := Encodable.encode_injective h
  have h2 := congrArg (List.map Prod.snd) h1
  rw [List.map_snd_zip (by simp), List.map_snd_zip (by simp)] at h2
  have h3 := List.ofFn_injective h2
  funext i
  exact Fin.ext (congrFun h3 i)

/-- `entryOf` on a zip with duplicate-free keys reads the matching position.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_zip {l₁ : List ℕ} (hnd : l₁.Nodup) :
    ∀ {l₂ : List ℕ} {i : ℕ} (hi : i < l₁.length) (hlen : l₂.length = l₁.length),
      entryOf l₁[i] (l₁.zip l₂) = some (l₂[i]'(by omega)) := by
  induction l₁ with
  | nil => intro l₂ i hi; simp at hi
  | cons a l ih =>
      intro l₂ i hi hlen
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          rw [List.nodup_cons] at hnd
          cases i with
          | zero => simp [entryOf]
          | succ j =>
              simp only [List.getElem_cons_succ, List.zip_cons_cons, entryOf]
              rw [if_neg, ih hnd.2 (by simpa using hi) (by simpa using hlen)]
              exact fun h => hnd.1 (h ▸ List.getElem_mem _)

/-- The entry of a coded function-table at `cs[i]` is `f ⟨i, hi⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_codeOf {cs : List ℕ} (hnd : cs.Nodup) (f : Fin cs.length → Fin d)
    {i : ℕ} (hi : i < cs.length) :
    entryOf (cs[i]'hi) (tableOfCode (codeOf cs f)) = some (f ⟨i, hi⟩ : ℕ) := by
  rw [tableOfCode_codeOf, entryOf_zip hnd hi (by simp)]
  simp [List.getElem_ofFn]

/-- **The tables over `cs`**: the codes of all function-tables.
Source: mandate K5a
Kind: D
Fidelity: n/a -/
noncomputable def tables (cs : List ℕ) (d : ℕ) : Finset ℕ :=
  (univ : Finset (Fin cs.length → Fin d)).image (codeOf cs)

/-- A sum over the coded tables is a sum over function-tables.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_tables (cs : List ℕ) (g : ℕ → ℝ) :
    ∑ q ∈ tables cs d, g q = ∑ f : Fin cs.length → Fin d, g (codeOf cs f) :=
  Finset.sum_image (codeOf_injective cs).injOn

/-- **A law on function-tables, pushed to codes** (`0` off the coded tables).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def lawOnCodes (cs : List ℕ) (μ : (Fin cs.length → Fin d) → ℝ) (q : ℕ) : ℝ :=
  if h : ∃ f, codeOf cs f = q then μ (Classical.choose h) else 0

/-- `lawOnCodes` at a coded table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lawOnCodes_codeOf (cs : List ℕ) (μ : (Fin cs.length → Fin d) → ℝ) (f : Fin cs.length → Fin d) :
    lawOnCodes cs μ (codeOf cs f) = μ f := by
  unfold lawOnCodes
  rw [dif_pos ⟨f, rfl⟩]
  congr 1
  exact codeOf_injective cs (Classical.choose_spec (⟨f, rfl⟩ : ∃ g, codeOf cs g = codeOf cs f))

/-- `lawOnCodes` is nonnegative when the law is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lawOnCodes_nonneg (cs : List ℕ) {μ : (Fin cs.length → Fin d) → ℝ} (hμ : ∀ f, 0 ≤ μ f) (q : ℕ) :
    0 ≤ lawOnCodes cs μ q := by
  unfold lawOnCodes
  split_ifs
  · exact hμ _
  · exact le_rfl

/-! ## The superbelief's marginals and balance on codes -/

/-- **The cell mass of a superbelief on codes** (`cellMass`'s shape with the superbelief in place
of `P n ∘ σ (n+1)`): the mass of the tables assigning `c` the cell `r`.
Source: mandate K5a (β); `Defs.cellMass`
Kind: D
Fidelity: exact (the shape of `cellMass`) -/
noncomputable def cellMassOf (states : Finset ℕ) (μ : ℕ → ℝ) (c r : ℕ) : ℝ :=
  ∑ q ∈ states.filter (fun q => entryOf c (tableOfCode q) = some r), μ q

/-- **The B2 value of a table at a coordinate**: the representative of the cell it lists
(`b2StateSystem`'s `val`; `0` if unlisted).
Source: bli-found `b2StateSystem` (`val m q φ` = `rep m` of the entry, `0` unlisted); mandate K5a (α)
Kind: D
Fidelity: exact -/
noncomputable def valOf (rep : ℕ → ℝ) (q c : ℕ) : ℝ :=
  match entryOf c (tableOfCode q) with
  | some r => rep r
  | none => 0

/-- `valOf` at a coded function-table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma valOf_codeOf {cs : List ℕ} (hnd : cs.Nodup) (rep : ℕ → ℝ) (f : Fin cs.length → Fin d)
    {i : ℕ} (hi : i < cs.length) : valOf rep (codeOf cs f) (cs[i]'hi) = rep (f ⟨i, hi⟩ : ℕ) := by
  unfold valOf
  rw [entryOf_codeOf hnd f hi]

/-- The cell mass of a pushed law at `cs[i]`, cell `r < d`, is the fibre mass of the law.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMassOf_lawOnCodes {cs : List ℕ} (hnd : cs.Nodup) (μ : (Fin cs.length → Fin d) → ℝ)
    {i : ℕ} (hi : i < cs.length) {r : ℕ} (hr : r < d) :
    cellMassOf (tables cs d) (lawOnCodes cs μ) (cs[i]'hi) r =
      ∑ f ∈ univ.filter (fun f : Fin cs.length → Fin d => f ⟨i, hi⟩ = ⟨r, hr⟩), μ f := by
  unfold cellMassOf
  rw [Finset.sum_filter, sum_tables, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [entryOf_codeOf hnd f hi, lawOnCodes_codeOf]
  by_cases h : f ⟨i, hi⟩ = ⟨r, hr⟩
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun h' => h (Fin.ext (Option.some.inj h'))]

/-- The balance of a pushed law at `cs[i]` is the law's balance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma balance_lawOnCodes {cs : List ℕ} (hnd : cs.Nodup) (μ : (Fin cs.length → Fin d) → ℝ)
    (rep : ℕ → ℝ) {i : ℕ} (hi : i < cs.length) :
    ∑ q ∈ tables cs d, lawOnCodes cs μ q * valOf rep q (cs[i]'hi) =
      ∑ f : Fin cs.length → Fin d, μ f * rep (f ⟨i, hi⟩ : ℕ) := by
  rw [sum_tables]
  exact Finset.sum_congr rfl fun f _ => by rw [lawOnCodes_codeOf, valOf_codeOf hnd]

/-! ## K5a -/

/-- **K5a (⇒) at a coordinate**: a superbelief on the coded tables whose cell masses at `cs[i]`
are `w r` (for `r < d`) and whose balance at `cs[i]` is `b` forces `b = ∑_{r<d} rep r · w r` —
the `D_NNUcell` identity at the coordinate, with no coherence and no coupling.
Source: mandate K5a ("(⇒) is K2(c)"); `ProductLaw.balance_of_marginals`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem d_nnucell_at_of_feasible {cs : List ℕ} (hnd : cs.Nodup) (μ : ℕ → ℝ)
    (hμ : ∀ q ∉ tables cs d, μ q = 0) (rep : ℕ → ℝ) {i : ℕ} (hi : i < cs.length) (w : ℕ → ℝ)
    (b : ℝ) (hmarg : ∀ r < d, cellMassOf (tables cs d) μ (cs[i]'hi) r = w r)
    (hbal : ∑ q ∈ tables cs d, μ q * valOf rep q (cs[i]'hi) = b) :
    b = ∑ r ∈ Finset.range d, rep r * w r := by
  -- pull `μ` back to function-tables
  have hpush : ∀ q, lawOnCodes cs (fun f : Fin cs.length → Fin d => μ (codeOf cs f)) q = μ q := by
    intro q
    unfold lawOnCodes
    split_ifs with h
    · simp only
      rw [Classical.choose_spec h]
    · exact (hμ q fun hq => h (by
        obtain ⟨f, -, hf⟩ := Finset.mem_image.1 hq
        exact ⟨f, hf⟩)).symm
  have hμν : μ = lawOnCodes cs (fun f : Fin cs.length → Fin d => μ (codeOf cs f)) := funext fun q => (hpush q).symm
  rw [hμν] at hbal hmarg
  rw [balance_lawOnCodes hnd _ rep hi] at hbal
  rw [← hbal, balance_of_marginals _ ⟨i, hi⟩ (fun r : Fin d => rep (r : ℕ)),
    ← Fin.sum_univ_eq_sum_range (fun r => rep r * w r) d]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hmarg r r.2, cellMassOf_lawOnCodes hnd _ hi r.2]

/-- **K5a (⇐), the product coupling of record.** On day `n`, over a cell family `C` with cells
`Finset.range d` and a duplicate-free index `cs = index (n+1)`: if the base's prices of
tomorrow's cell literals form a probability vector on every pinned coordinate (`hprob`) and
`D_NNUcell C index Q` holds, then for any balanced laws `ν` on the unpinned coordinates there
is a superbelief `μ` on `tables cs d`, nonnegative with total mass `1`, whose cell masses on
every pinned coordinate are the base's literal prices (β) and whose balance at the
representatives on every pinned coordinate is the base's price of the coordinate (α). `μ` is
`lawOnCodes (productLaw w)` — the mandate's `productCoupling` — with `w` the literal prices on
the pinned block and `ν` elsewhere.
Source: mandate K5a ("the projected kernel of record, `productCoupling`"); [[bli-program]] §3.6(v); construction C6; bli-slides-010/011; bli-soto-b-044
Kind: C
Fidelity: exact (the unpinned part is a parameter, as the mandate asks; cells `Finset.range d`)
Hyps: (a); `hprob` is the probability-vector clause (bli-slides-011's "consistent demands", FB-9), `hnd`/`hcells` are instance data -/
theorem exists_superbelief_of_d_nnucell {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲)
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
          Q n (sentenceOfCode c)) := by
  classical
  set cs := index (n + 1) with hcs
  -- the marginal data: literal prices on the pinned block, `ν` elsewhere
  set w : Fin cs.length → Fin d → ℝ := fun i r =>
    if cs[i.1]'i.2 ∈ pinned C index n then
      Q n (C.literal (n + 1) (sentenceOfCode (cs[i.1]'i.2)) r)
    else ν (cs[i.1]'i.2) r with hw
  have hw0 : ∀ i r, 0 ≤ w i r := by
    intro i r
    simp only [hw]
    split_ifs with h
    · exact (hprob _ h).1 r r.2
    · exact (hν _).1 r r.2
  have hw1 : ∀ i, ∑ r, w i r = 1 := by
    intro i
    simp only [hw]
    split_ifs with h
    · rw [Fin.sum_univ_eq_sum_range
        (fun r => Q n (C.literal (n + 1) (sentenceOfCode (cs[i.1]'i.2)) r)) d]
      exact (hprob _ h).2
    · rw [Fin.sum_univ_eq_sum_range (fun r => ν (cs[i.1]'i.2) r) d]
      exact (hν _).2
  refine ⟨lawOnCodes cs (productLaw w), lawOnCodes_nonneg cs (productLaw_nonneg hw0), ?_, ?_, ?_⟩
  · rw [sum_tables]
    simp only [lawOnCodes_codeOf]
    exact sum_productLaw hw1
  · intro c hc r hr
    have hmem : c ∈ cs := ((mem_pinned C index n c).1 hc).1
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hmem
    rw [cellMassOf_lawOnCodes hnd _ hi hr, marginal_productLaw hw1]
    simp only [hw]
    rw [if_pos hc]
  · intro c hc
    have hmem : c ∈ cs := ((mem_pinned C index n c).1 hc).1
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hmem
    rw [balance_lawOnCodes hnd _ _ hi,
      balance_productLaw hw1 ⟨i, hi⟩ (fun r : Fin d => (C.rep (n + 1) (r : ℕ) : ℝ)),
      hdnnu n _ hc, hcells, ← Fin.sum_univ_eq_sum_range
        (fun r => (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode (cs[i]'hi)) r)) d]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hw]
    rw [if_pos hc]

/-! ## N+: two coordinates, two cells, four tables all charged -/

/-- The uniform marginal data `1/2` on two cells.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def halfW (k : ℕ) : Fin k → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- Each `halfW` row is a probability vector.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma halfW_sum (k : ℕ) (i : Fin k) : ∑ r, halfW k i r = 1 := by
  simp [halfW]

/-- The product coupling of `halfW k` is `(1/2)^k` on every table.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma productLaw_halfW (k : ℕ) (f : Fin k → Fin 2) : productLaw (halfW k) f = (1 / 2) ^ k := by
  simp [productLaw, halfW]

/-- **N+ (K5a/b): over two distinct coordinates and two cells, the product coupling of the
uniform marginals charges every one of the four tables `1/4`.**
Source: mandate K5b ("a base with ≥ 2 cells of positive mass on ≥ 2 coordinates (`4` tables charged)")
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem fourTables_charged (c₁ c₂ : ℕ) (f : Fin [c₁, c₂].length → Fin 2) :
    lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)) (codeOf [c₁, c₂] f) = 1 / 4 := by
  rw [lawOnCodes_codeOf, productLaw_halfW]
  simp
  norm_num

/-- **N+ (K5a (β))**: its cell masses on both coordinates are `1/2` at each cell.
Source: mandate K5a/b
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem fourTables_marginals (c₁ c₂ : ℕ) (hne : c₁ ≠ c₂) {r : ℕ} (hr : r < 2) :
    cellMassOf (tables [c₁, c₂] 2) (lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)))
        c₁ r = 1 / 2 ∧
      cellMassOf (tables [c₁, c₂] 2) (lawOnCodes [c₁, c₂] (productLaw (halfW [c₁, c₂].length)))
        c₂ r = 1 / 2 := by
  have hnd : [c₁, c₂].Nodup := by simp [hne]
  constructor
  · have h := cellMassOf_lawOnCodes (d := 2) hnd (productLaw (halfW [c₁, c₂].length)) (i := 0)
      (by simp) hr
    simp only [List.getElem_cons_zero] at h
    rw [h, marginal_productLaw (halfW_sum _)]
    rfl
  · have h := cellMassOf_lawOnCodes (d := 2) hnd (productLaw (halfW [c₁, c₂].length)) (i := 1)
      (by simp) hr
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [h, marginal_productLaw (halfW_sum _)]
    rfl

/-- **The hypotheses of `exists_superbelief_of_d_nnucell` are inhabited** by the constant base
`Q ≡ 1/2` (uncertain about every coordinate and every cell) at representatives `1/4`, `3/4`
(`Witness.wCF`), any day and any index: the literal prices form a probability vector and
`D_NNUcell` holds (`1/2 = 1/4 · 1/2 + 3/4 · 1/2`). The base is a constant market (disclosed:
not coherent, not an inductor); the data on one day is all the theorem reads.
Source: mandate K5a/b (N+); [[STANDARDS]] §3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem halfBase_hypotheses (index : ℕ → List ℕ) (n : ℕ) :
    (∀ c ∈ pinned Witness.wCF index n,
      (∀ r < 2, (0 : ℝ) ≤ (fun _ _ => (1 / 2 : ℝ) : History) n
        (Witness.wCF.literal (n + 1) (sentenceOfCode c) r)) ∧
        ∑ r ∈ Finset.range 2, (fun _ _ => (1 / 2 : ℝ) : History) n
          (Witness.wCF.literal (n + 1) (sentenceOfCode c) r) = 1) ∧
      D_NNUcell Witness.wCF index (fun _ _ => (1 / 2 : ℝ)) := by
  refine ⟨fun c _ => ⟨fun _ _ => by norm_num, ?_⟩, fun m c _ => ?_⟩
  · simp
  · simp only [Witness.wCF_cells, Dissolve.dCells, Witness.wCF_rep,
      Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), Dissolve.dRep]
    norm_num

end Existence

end Cleanroom.Bli.BliLinkageB
