import Cleanroom.Bli.BliExactBase.Segment
import Cleanroom.Bli.BliAssemble.Headline
import Cleanroom.Bli.BliTrajectory.DenominatorMesh
import Cleanroom.Bli.BliTrajectory.Update

/-!
# `bli-exact-base` · Bli: K7e — the tent BLI over the spliced base (transport); the exact
small-sentence update on the segment

**K7e** (mandate § 5): the object is `spliceBli H t 𝓜 c := bliHistory (spliceRat H t) 𝓜
(tentSkeleton smallIndex 𝓜) c` — `bli-trajectory`'s construction with the **splice** as its base
(`spliceRat H t`, whose cast is `spliceHistory H t` definitionally, `ratHistory_spliceRat`).

* (iii) **The criterion**: `spliceBli_isLogicalInductor_of` is `bli-assemble`'s row of record
  `bliHistory_isLogicalInductor_of` at the instance `spliceRat_isLogicalInductor` (K7a, through
  `spliceHistory_eq_cast : rfl`), **given** a splice certificate `C` for the tent expression map
  and a computable table `hov` for the re-pricing — both are `bli-assemble`'s obligations, OPEN
  there (`tentOracle_exists`, `bliOv_computableTable`), never restated here. Ledger Status:
  `partial: rewrite certificate open`.
* (i) **The bundle**: `spliceBli_package` transports `bliHistory_tent_package` — the scoped Roman
  bundle, product-face non-degeneracy of every day's superbelief, the small update up to the
  mesh, the range — with the range derived from the inductor instance (never assumed).
* (ii) **The exact small-sentence update on segment days** — the only place K7 gives "exactly
  Bayesian on days `< H`": `bli_update_small_exact_of_gridVal` (general: over any base, mesh,
  skeleton and coding, the product-form update `𝐏_{n+1}(φ) · 𝐏_n(σ) = 𝐏_n(φ ⋏ σ)` holds
  **exactly** at a day-`n` small `φ` whose day-`(n+1)` base price is a grid value — the rounding
  error of `bli_update_small`'s proof is zero there), and its instances: `spliceBli_update_exact`
  (on a segment day whenever the table's next-day value is on the grid), at the splice's own
  **denominator mesh** (`bli-trajectory`'s noncomputable `denominatorMesh`, every day:
  `spliceBli_update_exact_denominator`, with the exact Tier-A total update
  `spliceBli_TB_tierA_denominator`), and at the computable **`segmentMesh K`** (`d n := 2^(n+K)`)
  for the linked table on every segment day (`linkedBli_update_exact_segment`, with the `K` whose
  existence `exists_segment_K` proves — the dyadic refinement of the family, `Segment.kAt`).
  **Repair round 1 (audit r1 adversarial B2):** at the *linked* table the product form is
  `x · 0 = 0` on every segment day from some `N` on — the kernel's override by shape puts the
  realized day-`(n+1)` linked table off the product face of the day-`n` one, so the tent law
  charges it `0` (`Uncharged.tent_actual_next_zero`, every mesh). The exact update with content
  is over the **unlinked** segment tables at the denominator mesh: `𝐏_n(σ) > 0` on every segment
  day and the ratio form holds (`Uncharged.segmentTent_actual_next_pos`,
  `Uncharged.segmentTent_update_ratio`); findings F22.

**What this BLI is not** (mandate § 5): it is **not linked** (the tent skeleton charges incoherent
tables — the superbelief's product face contains tables with `⊤ ≠ 1`, so the state algebra is
not `PCPσ`-coherent; K7d's `Linked.charged_top_cell_rep_one` is why the two cannot coexist) and
its criterion is `partial`. It is the object `udt-bli-sist`/`bli-witness-lia` consume for U15's
*unlinked* form; K7d's `Segment` data is what the linked form needs.

Sources: [[bli-program]] §3.6 (vi), §5; mandate § 5, § Definitions (`segmentMesh`,
`bli_update_small_exact_of_grid`); [[bli-exact-base-handoff]] items 3–4.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliAssemble Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

namespace Bli

open Classical

noncomputable section

/-! ## The splice as a `RatHistory` base -/

/-- The cast of the rational splice is the splice (definitional).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ratHistory_spliceRat (H : ℕ) (t : ℕ → Sentence → ℚ) :
    ratHistory (spliceRat H t) = spliceHistory H t := rfl

/-- On a segment day the rational splice is the table on the small sentences.
Source: none: infrastructure (`Splice.spliceHistory_eq_tbl_of_lt`)
Kind: L
Fidelity: n/a -/
theorem spliceRat_eq_tbl_of_lt {H : ℕ} {t : ℕ → Sentence → ℚ} {n : ℕ} {φ : Sentence}
    (hn : n < H) (hφ : φ ∈ smallSet n) : spliceRat H t n φ = t n φ := by
  have h := spliceHistory_eq_tbl_of_lt (H := H) (t := t) hn hφ
  rw [spliceHistory_eq_cast] at h
  exact_mod_cast h

/-- **K7a as the inductor instance of the `RatHistory` form**: `ratHistory (spliceRat H t)` is a
logical inductor over `paperDP 𝗜𝚺₁` for every horizon and every table in `[0,1]` on the small
sentences (finitely many `(day, sentence)` pairs re-priced, `segmentPatch H`).
Source: mandate § 1, § 5 ("through `spliceHistory_eq_cast : rfl`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceRat_isLogicalInductor (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    IsLogicalInductor (ratHistory (spliceRat H t)) (paperDP 𝗜𝚺₁) :=
  splice_isLogicalInductor H t ht

/-- The splice's range `[0,1]` on every day and sentence, derived from the inductor instance.
Source: none: infrastructure (`bli-assemble`'s `range_of_isLogicalInductor`)
Kind: L
Fidelity: n/a -/
theorem spliceRat_range (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    ∀ n φ, 0 ≤ spliceRat H t n φ ∧ spliceRat H t n φ ≤ 1 :=
  @range_of_isLogicalInductor (spliceRat H t) (paperDP 𝗜𝚺₁) (spliceRat_isLogicalInductor H t ht)

/-! ## K7e: the tent BLI over the splice -/

/-- **The tent BLI over the spliced base** (K7e's object): `bli-trajectory`'s `bliHistory` at the
base `spliceRat H t`, the tent skeleton on `smallIndex`, mesh `𝓜` and coding `c`.
Source: mandate § 5 (K7e)
Kind: D
Fidelity: exact -/
abbrev spliceBli (H : ℕ) (t : ℕ → Sentence → ℚ) (𝓜 : Mesh) (c : StateCoding 𝓜) : History :=
  bliHistory (spliceRat H t) 𝓜 (tentSkeleton smallIndex 𝓜) c

/-- **K7e (iii) — the criterion, transported**: the tent BLI over the splice is a logical inductor
over `paperDP 𝗜𝚺₁`, **given** a splice certificate `C` for the tent expression map and a
computable table `hov` for the re-pricing — `bli-assemble`'s row of record
`bliHistory_isLogicalInductor_of` at the instance `spliceRat_isLogicalInductor` (K7a). The two
named hypotheses are `bli-assemble`'s obligations, OPEN there (`tentOracle_exists`,
`bliOv_computableTable` at `dyadicMesh`/`writeOutCoding`); nothing here discharges or restates
them. Status: `partial: rewrite certificate open`.
Source: [[bli-program]] §3.6 (vi) ("is an LI by L2"), §5; mandate § 5 (iii)
Kind: C
Fidelity: weaker: unlinked (the tent charges incoherent tables); criterion partial (`C`, `hov` named)
Hyps: (a) `ht` (the range clause of `def:market`, discharged by every table of this package); `C`, `hov` named — `bli-assemble`'s OPEN obligations, inherited (mandate Known issue 7); no (b), no (c) -/
theorem spliceBli_isLogicalInductor_of (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (C : SpliceCertificate (tentExprMap 𝓜 c))
    (hov : ComputableTable (bliOv (spliceRat H t) 𝓜 (tentSkeleton smallIndex 𝓜) c)) :
    IsLogicalInductor (spliceBli H t 𝓜 c) (paperDP 𝗜𝚺₁) :=
  @bliHistory_isLogicalInductor_of (spliceRat H t) (paperDP 𝗜𝚺₁) 𝓜 c
    (spliceRat_isLogicalInductor H t ht) C hov

/-- **K7e (i) — the non-degeneracy bundle, transported**: `bli-assemble`'s `bliHistory_tent_package`
at the splice — the scoped Roman bundle `E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5` against the
splice as base, product-face non-degeneracy of every day's superbelief, the small-sentence update
up to the mesh, the range — with the range derived from the inductor instance.
Source: mandate § 5 (i); `bli-assemble` target 7
Kind: C
Fidelity: weaker: faith scoped, non-degeneracy on the product face (as `bli-trajectory`'s rows)
Hyps: (a) `ht` -/
theorem spliceBli_package (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) (𝓜 : Mesh) (c : StateCoding 𝓜) :
    IsBLI_RomanScoped c (bliStateSystem (spliceRat H t) 𝓜 c) (spliceHistory H t)
        (spliceBli H t 𝓜 c) ∧
      (∀ n, NonDegenerate 𝓜.d
        (fun A => bliPrice (spliceRat H t) 𝓜 (tentSkeleton smallIndex 𝓜) c n
          (stateAtom (n + 1) (c.code (n + 1) A)))
        (actualTable smallIndex (spliceRat H t) n)) ∧
      (∀ n, ∀ φ ∈ smallSet n,
        |spliceBli H t 𝓜 c (n + 1) φ *
            spliceBli H t 𝓜 c n
              (stateAtom (n + 1) ((bliStateSystem (spliceRat H t) 𝓜 c).actual (n + 1))) -
          spliceBli H t 𝓜 c n
            (φ ⋏ stateAtom (n + 1) ((bliStateSystem (spliceRat H t) 𝓜 c).actual (n + 1)))|
          ≤ (1 / (2 * (𝓜.d (n + 1) : ℝ))) *
            spliceBli H t 𝓜 c n
              (stateAtom (n + 1) ((bliStateSystem (spliceRat H t) 𝓜 c).actual (n + 1)))) ∧
      (∀ n ψ, 0 ≤ spliceBli H t 𝓜 c n ψ ∧ spliceBli H t 𝓜 c n ψ ≤ 1) :=
  bliHistory_tent_package (spliceRat H t) 𝓜 c (spliceRat_range H t ht)

/-! ## The exact small-sentence update at a grid price (general) -/

section ExactUpdate

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (sk : Skeleton smallIndex 𝓜.d) (Q : RatHistory)

/-- **The small-sentence update is exact at a grid price** (the per-day
`bli_update_small_exact_of_grid` of the mandate, over any base, mesh, skeleton and coding): for a
day-`n` small `φ` whose day-`(n+1)` base price is a value of the day-`(n+1)` grid, the product
form `𝐏_{n+1}(φ) · 𝐏_n(σ) = 𝐏_n(φ ⋏ σ)` holds **exactly** (`σ` the realized day-`(n+1)` state
atom). `bli_update_small`'s mechanism with zero rounding error: the joint reads the rounded actual
table, and rounding is the identity on a grid value (`roundVal_eq_self`). No positivity needed
(product form); the ratio form is `bli-trajectory`'s `bli_update_small_exact_iff`.
Source: mandate § Definitions (`bli_update_small_exact_of_grid`), § 5 (ii); Appendix B
(`main.tex:440–442`); bli-slides-004
Kind: P
Fidelity: exact (per day, at a grid price; the all-days `E1r`-style form is `bli_E1r_of_grid`)
Hyps: (a) `hg` (the grid clause, discharged on segment days by the tables below) -/
theorem bli_update_small_exact_of_gridVal (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n)
    (hg : Q (n + 1) φ ∈ gridVals (𝓜.d (n + 1))) :
    bliHistory Q 𝓜 sk c (n + 1) φ *
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) =
      bliHistory Q 𝓜 sk c n (φ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) := by
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hA : actualState smallIndex 𝓜.d Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  simp only [bliStateSystem_actual]
  have hq : c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)) ∈ c.states (n + 1) :=
    c.code_mem_states hA
  have hno : NoFutureState c n φ := noFutureState_of_smallOn c (mem_smallSet.mp hφ)
  have h1 : bliHistory Q 𝓜 sk c (n + 1) φ = (Q (n + 1) φ : ℝ) := by
    unfold bliHistory; rw [bliPrice_of_small (mem_smallSet.mp hφ')]
  have h3 : bliHistory Q 𝓜 sk c n
      (φ ⋏ stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)))) =
      ((actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, hφ'⟩ : ℚ) : ℝ) *
        bliHistory Q 𝓜 sk c n
          (stateAtom (n + 1) (c.code (n + 1) (actualState smallIndex 𝓜.d Q (n + 1)))) := by
    unfold bliHistory
    rw [bliPrice_and_stateAtom c sk Q (Nat.lt_succ_self n) hq hno (mem_smallSet.mp hφ'),
      c.tableVal_code hA hφ']
    push_cast; ring
  have hround : actualState smallIndex 𝓜.d Q (n + 1) ⟨φ, hφ'⟩ = Q (n + 1) φ := by
    show roundVal (𝓜.d (n + 1)) (Q (n + 1) φ) = Q (n + 1) φ
    exact roundVal_eq_self (𝓜.d_pos _) hg
  rw [h1, h3, hround]

end ExactUpdate

/-! ## The exact update over the splice -/

/-- **K7e (ii) — the exact small-sentence update on a segment day**: for `n + 1 < H` and a day-`n`
small `φ` whose day-`(n+1)` table value lies on the day-`(n+1)` grid, the tent BLI over the splice
updates exactly in product form. The grid clause is what a mesh choice discharges (below).
Source: mandate § 5 (ii) ("exactly Bayesian on days `< H`")
Kind: C
Fidelity: exact (per day; product form)
Hyps: (a) `hg` -/
theorem spliceBli_update_exact (H : ℕ) (t : ℕ → Sentence → ℚ) (𝓜 : Mesh) (c : StateCoding 𝓜)
    {n : ℕ} (hn : n + 1 < H) {φ : Sentence} (hφ : φ ∈ smallSet n)
    (hg : t (n + 1) φ ∈ gridVals (𝓜.d (n + 1))) :
    spliceBli H t 𝓜 c (n + 1) φ *
        spliceBli H t 𝓜 c n
          (stateAtom (n + 1) ((bliStateSystem (spliceRat H t) 𝓜 c).actual (n + 1))) =
      spliceBli H t 𝓜 c n
        (φ ⋏ stateAtom (n + 1) ((bliStateSystem (spliceRat H t) 𝓜 c).actual (n + 1))) :=
  bli_update_small_exact_of_gridVal c _ (spliceRat H t) n hφ
    (by rw [spliceRat_eq_tbl_of_lt hn (smallSet_mono (Nat.le_succ n) hφ)]; exact hg)

/-- **K7e (ii) at the splice's denominator mesh — every day**: at `bli-trajectory`'s
noncomputable `denominatorMesh (spliceRat H t)` every actual table is a grid table, so the
small-sentence update is exact on **every** day (segment days and the LIA's days alike; the mesh
adapts to the base). The mandate's "remark on both": this form needs no segment, and its mesh is
not computable — the certificate/table obligations of the criterion are then for a noncomputable
mesh (`bli-assemble` target 11). Product form: at `t := Segment.linkedPrice` it is `x · 0 = 0` on
every segment day from some `N` on (`Uncharged.tent_actual_next_zero`'s mechanism holds at every
mesh); at `t := segmentPrice` the realized next state has positive mass on every segment day and
the ratio form holds (`Uncharged.segmentTent_update_ratio`).
Source: mandate § Definitions (`denominatorMesh`, "the noncomputable all-days alternative"), § 5 (ii)
Kind: C
Fidelity: exact (every day; noncomputable mesh; product form — non-vacuous at `segmentPrice` on
segment days, vacuous at `linkedPrice` from some `N` on)
Hyps: (a) `ht` -/
theorem spliceBli_update_exact_denominator (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1)
    (c : StateCoding (denominatorMesh (spliceRat H t))) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    spliceBli H t (denominatorMesh (spliceRat H t)) c (n + 1) φ *
        spliceBli H t (denominatorMesh (spliceRat H t)) c n
          (stateAtom (n + 1)
            ((bliStateSystem (spliceRat H t) (denominatorMesh (spliceRat H t)) c).actual (n + 1))) =
      spliceBli H t (denominatorMesh (spliceRat H t)) c n
        (φ ⋏ stateAtom (n + 1)
          ((bliStateSystem (spliceRat H t) (denominatorMesh (spliceRat H t)) c).actual (n + 1))) :=
  bli_update_small_exact_of_gridVal c _ (spliceRat H t) n hφ
    (mem_grid_iff.mp (actualTable_mem_grid_denominatorMesh _ (spliceRat_range H t ht) (n + 1))
      ⟨φ, smallSet_mono (Nat.le_succ n) hφ⟩)

/-- **The exact Tier-A total update at the splice's denominator mesh** (`bli-trajectory`'s
`bli_TB_on_tierA_denominator` at the splice): on every day, for every Tier-A sentence whose small
part mentions no day-`(n+1)` atom, `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` exactly.
Source: [[bli-program]] §3.5 (iii); `bli-assemble` target 11; mandate § 5 (ii)
Kind: C
Fidelity: exact (Tier A, at a noncomputable mesh)
Hyps: (a) `ht` -/
theorem spliceBli_TB_tierA_denominator (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1)
    (c : StateCoding (denominatorMesh (spliceRat H t))) :
    TB_on (TierAUpdatable c) (bliStateSystem (spliceRat H t) (denominatorMesh (spliceRat H t)) c)
      (spliceBli H t (denominatorMesh (spliceRat H t)) c) :=
  bli_TB_on_tierA_denominator c _ (spliceRat_range H t ht)

/-! ## The segment mesh and the dyadic linked table -/

/-- **The segment mesh** `d n := 2 ^ (n + K)` (the mandate's `segmentMesh H K`; `d` does not
depend on `H` — `K` is chosen per horizon by `exists_segment_K`): computable, positive, nested.
`dyadicMesh` is `K = 0`.
Source: mandate § Definitions (`segmentMesh`)
Kind: D
Fidelity: exact -/
def segmentMesh (K : ℕ) : Mesh where
  d n := 2 ^ (n + K)
  d_pos n := Nat.two_pow_pos _
  d_dvd n := pow_dvd_pow 2 (by omega)

/-- **The kernel market's rational table lies on the grid of denominator `2k`**: the uniform
mixture over `2k` worlds with `{0,1}` payouts is a count over `2k`.
Source: mandate § 2 (dyadic weights), § 4 ("pick `d n` so `marginalOf` lands on the grid")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem kMixRat_mem_gridVals (D : Finset Sentence) (m : ℕ) {k : ℕ} (W : Fin k → PCWorld)
    (φ : Sentence) : Kernel.kMixRat D m W φ ∈ gridVals (2 * k) := by
  rw [mem_gridVals_iff]
  refine ⟨(Finset.univ.filter fun x : Fin k × Bool => (Kernel.kWorld D m W x).Holds φ).card,
    ?_, ?_⟩
  · calc _ ≤ (Finset.univ : Finset (Fin k × Bool)).card := Finset.card_filter_le _ _
      _ = 2 * k := by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  · unfold Kernel.kMixRat
    simp only [PCWorld.payoutRat]
    rw [← Finset.mul_sum, Finset.sum_boole]
    push_cast
    ring

/-- **The linked table is dyadic**: on every day `n` and sentence `φ`, `linkedPrice n φ` lies on
the grid of denominator `2 ^ (k₀ n + 1)` (the family of record has `2 ^ k₀ n` members,
`Segment.kAt`).
Source: mandate § 2 ("this is what fixes `segmentMesh`'s `K`"); [[bli-exact-base-handoff]] item 4
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem linkedPrice_mem_gridVals (n : ℕ) (φ : Sentence) :
    Segment.linkedPrice n φ ∈ gridVals (2 ^ (Segment.k₀ n + 1)) := by
  have h := kMixRat_mem_gridVals ((paperDP 𝗜𝚺₁).D n) (n + 1) (Segment.WAt n) φ
  rwa [show 2 * Segment.kAt n = 2 ^ (Segment.k₀ n + 1) by rw [Segment.kAt, pow_succ, mul_comm]]
    at h

/-- **For every horizon there is a `K` putting the linked tables on `segmentMesh K`**: with
`K := ∑_{m < H} (k₀ m + 1)`, every day-`n` linked price (`n < H`) is a value of the day-`n` grid
`2 ^ (n + K)`. `K` is a choice (through `k₀`); for each fixed `K` the mesh is computable.
Source: mandate § Definitions ("choose `K` so every hand-built value has denominator dividing `2 ^ K`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_segment_K (H : ℕ) :
    ∃ K, ∀ n < H, ∀ φ, Segment.linkedPrice n φ ∈ gridVals ((segmentMesh K).d n) := by
  refine ⟨∑ m ∈ Finset.range H, (Segment.k₀ m + 1), fun n hn φ => ?_⟩
  have hle : Segment.k₀ n + 1 ≤ ∑ m ∈ Finset.range H, (Segment.k₀ m + 1) :=
    Finset.single_le_sum (f := fun m => Segment.k₀ m + 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hn)
  exact gridVals_mono (pow_dvd_pow 2 (by omega)) (Nat.two_pow_pos _) (linkedPrice_mem_gridVals n φ)

/-- **The linked table's actual tables are grid tables on the segment** at a `segmentMesh K`
with `K` as in `exists_segment_K`: for `n < H`, `actualTable smallIndex (spliceRat H linkedPrice) n ∈ grid`.
Source: mandate § Definitions ("then `roundTo` is the identity on the segment tables")
Kind: L
Fidelity: n/a -/
theorem linked_actualTable_mem_grid {H K : ℕ}
    (hK : ∀ n < H, ∀ φ, Segment.linkedPrice n φ ∈ gridVals ((segmentMesh K).d n))
    {n : ℕ} (hn : n < H) :
    actualTable smallIndex (spliceRat H Segment.linkedPrice) n ∈ grid smallIndex (segmentMesh K).d n := by
  rw [mem_grid_iff]
  intro φ
  show spliceRat H Segment.linkedPrice n φ.1 ∈ gridVals ((segmentMesh K).d n)
  rw [spliceRat_eq_tbl_of_lt hn φ.2]
  exact hK n hn φ.1

/-- **K7e (ii) at the linked splice — the product-form update at the computable `segmentMesh K`**
(`K` from `exists_segment_K`): for `n + 1 < H` and every day-`n` small `φ`,
`𝐏_{n+1}(φ) · 𝐏_n(σ) = 𝐏_n(φ ⋏ σ)`. **Vacuous from some `N` on** (repair round 1, audit r1
adversarial B2): for `n ≥ N` the realized day-`(n+1)` linked table is off the product face of the
day-`n` one (the kernel's override by shape prices every day-`(n+1)` `⊤`-literal atom at `1`
today and strictly inside tomorrow), so `𝐏_n(σ) = 0` and both sides are `0`
(`Uncharged.tent_actual_next_zero`); the ratio form is undefined there. The "exactly Bayesian on
days `< H`" clause of [[bli-program]] §3.6 (vi) with content is `Uncharged.segmentTent_update_ratio`
over the *unlinked* segment tables (noncomputable mesh); under Route W by shape "linked" and
"exactly Bayesian" conflict (findings F22). Kept as the instance of record of the computable-mesh
mechanism; the LIA's days `≥ H` are off every computable grid (`bli_E1r_of_grid` is global and
does not apply).
Source: [[bli-program]] §3.6 (vi) ("exactly Bayesian"); mandate § 5 (ii)
Kind: C
Fidelity: weaker: product form; vacuous (`𝐏_n(σ) = 0`) on every segment day `n ≥ N`
(`Uncharged.tent_actual_next_zero`)
Hyps: (a) `hK` (discharged by `exists_segment_K`) -/
theorem linkedBli_update_exact_segment {H K : ℕ}
    (hK : ∀ n < H, ∀ φ, Segment.linkedPrice n φ ∈ gridVals ((segmentMesh K).d n))
    (c : StateCoding (segmentMesh K)) {n : ℕ} (hn : n + 1 < H) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    spliceBli H Segment.linkedPrice (segmentMesh K) c (n + 1) φ *
        spliceBli H Segment.linkedPrice (segmentMesh K) c n
          (stateAtom (n + 1)
            ((bliStateSystem (spliceRat H Segment.linkedPrice) (segmentMesh K) c).actual (n + 1))) =
      spliceBli H Segment.linkedPrice (segmentMesh K) c n
        (φ ⋏ stateAtom (n + 1)
          ((bliStateSystem (spliceRat H Segment.linkedPrice) (segmentMesh K) c).actual (n + 1))) :=
  spliceBli_update_exact H Segment.linkedPrice (segmentMesh K) c hn hφ (hK (n + 1) hn φ)

/-- **K7e packaged at the linked splice** (the honest form of the program's K7 sentence, mandate
§ 5): for every horizon `H` there is a `K` such that the tent BLI over the linked splice at
`segmentMesh K` (i) carries the scoped Roman bundle, product-face non-degeneracy and the range,
(ii) satisfies the product-form update on every segment day — **vacuous from some `N` on**
(`Uncharged.tent_actual_next_zero`; see `linkedBli_update_exact_segment`) — and (iii) is a logical
inductor over `paperDP 𝗜𝚺₁` given the certificate and the table (`bli-assemble`'s OPEN
obligations, named).
Source: [[bli-program]] §3.6 (vi), §5; mandate § 5
Kind: C
Fidelity: weaker: unlinked; faith scoped; (ii) product form, vacuous for `n ≥ N`; criterion
partial (`C`, `hov` named)
Hyps: (a); `C`, `hov` named (inherited OPEN) -/
theorem linkedBli_package (H : ℕ) :
    ∃ K, ∀ c : StateCoding (segmentMesh K),
      IsBLI_RomanScoped c (bliStateSystem (spliceRat H Segment.linkedPrice) (segmentMesh K) c)
          (Segment.linkedSplice H) (spliceBli H Segment.linkedPrice (segmentMesh K) c) ∧
        (∀ n, NonDegenerate (segmentMesh K).d
          (fun A => bliPrice (spliceRat H Segment.linkedPrice) (segmentMesh K)
            (tentSkeleton smallIndex (segmentMesh K)) c n (stateAtom (n + 1) (c.code (n + 1) A)))
          (actualTable smallIndex (spliceRat H Segment.linkedPrice) n)) ∧
        (∀ n, n + 1 < H → ∀ φ ∈ smallSet n,
          spliceBli H Segment.linkedPrice (segmentMesh K) c (n + 1) φ *
              spliceBli H Segment.linkedPrice (segmentMesh K) c n
                (stateAtom (n + 1)
                  ((bliStateSystem (spliceRat H Segment.linkedPrice) (segmentMesh K) c).actual
                    (n + 1))) =
            spliceBli H Segment.linkedPrice (segmentMesh K) c n
              (φ ⋏ stateAtom (n + 1)
                ((bliStateSystem (spliceRat H Segment.linkedPrice) (segmentMesh K) c).actual
                  (n + 1)))) ∧
        (∀ (C : SpliceCertificate (tentExprMap (segmentMesh K) c))
          (_ : ComputableTable (bliOv (spliceRat H Segment.linkedPrice) (segmentMesh K)
            (tentSkeleton smallIndex (segmentMesh K)) c)),
          IsLogicalInductor (spliceBli H Segment.linkedPrice (segmentMesh K) c) (paperDP 𝗜𝚺₁)) := by
  obtain ⟨K, hK⟩ := exists_segment_K H
  refine ⟨K, fun c => ?_⟩
  have hp := spliceBli_package H Segment.linkedPrice (Segment.linkedPrice_inUnit H) (segmentMesh K) c
  exact ⟨hp.1, hp.2.1, fun n hn φ hφ => linkedBli_update_exact_segment hK c hn hφ,
    fun C hov => spliceBli_isLogicalInductor_of H Segment.linkedPrice
      (Segment.linkedPrice_inUnit H) (segmentMesh K) c C hov⟩

end

end Bli

end Cleanroom.Bli.BliExactBase
