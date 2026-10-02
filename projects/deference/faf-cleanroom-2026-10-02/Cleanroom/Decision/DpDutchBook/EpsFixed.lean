import Cleanroom.Decision.DpDutchBook.MsrExists
import Cleanroom.Decision.DpCalibration.Devices
import Mathlib.Topology.Sequences

/-!
# T8: ε-calibrated-and-approved procedures exist; `testSeq_exists_open` discharged (over `ℝ`)

* `productSimplex` — the domain `∏_d Δ(A_d)` of `kakutani_pi_stdSimplex`; `toProcP` reads a
  point as a procedure; `trRaw ε x` are the raw weights of its tremble `C^ε`.
* `realized d` — the acts `b` with a chance-positive leaf in `b ∧ O_d`: for a *full-support*
  procedure these are exactly the acts with `ν(b ∧ O_d) > 0` (`nu_pos_iff_realized`), so the
  domain of D2At's comparison is the same at every point of the simplex.
* `vRaw ε d b x` — the strictly calibrated act value `𝔼_{C^ε}[r ∣ b ∧ O_d]` as a function of the
  raw label; continuous on the simplex where `b` is realized (`vRaw_continuousOn`).
* `QPt B`, `productSimplexQ`, `extQ` — the queried points as a finite type, the product of
  simplices over them (finite-dimensional for every `ι`), and the extension of a queried-point
  label to all of `ι` by a fixed point mass (unqueried points never enter the run law).
* `fpFace ε y` — the face of the queried-point product simplex carrying weight, at each queried
  `d` with a realized act, only on realized maximisers of `vRaw ε d · (extQ y)` (Definition 18's
  escape clause where no act is realized within `O_d`). Nonempty, convex, closed graph — proved.
* `d2At_exists` — **T8(a), per-ε existence**: for every `ε ∈ (0, 1]` some `C'` satisfies
  `D2At obs actEv B C' ε` (Kakutani on `fpFace ε`), with `ι` arbitrary. No ε-floor and no
  de-trembling are needed: the fixed point is taken directly in the D2At form (values at the
  tremble `C'^ε`, support of `C'` itself).
* `testSeq_exists` — **T8(b), the discharge of `dp-calibration`'s OPEN row**: `ε_n = 1/(n+2)`,
  the fixed points `y_n`, a convergent subsequence by compactness of the queried-point product
  simplex, and `TestSeqTrembleEdtConsistent` for the extension of its limit.
  `testSeq_exists_open_discharged` has exactly `testSeq_exists_open`'s statement — the same
  instance arguments (no `Fintype ι`), the same argument order, the unused `_hpruned` present.
  (Audit round 1 found the earlier version carried `[Fintype ι]`; repaired 2026-10-01.)
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Found.FixKakutani
open Finset Filter Topology

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-! ## The product simplex and its procedures -/

section domain

/-- The product of the standard simplices, `∏_d Δ(A_d)`.
Source: `seeds.md` SE-18′(a) (the domain of the fixed-point map); `fix-kakutani`'s
`kakutani_pi_stdSimplex`
Kind: D -/
def productSimplex : Set ((d : ι) → acts d → ℝ) := Set.univ.pi fun d => stdSimplex ℝ (acts d)

/-- A point of the product simplex as a procedure. Source: none: infrastructure. Kind: D -/
def toProcP (x : (d : ι) → acts d → ℝ) (hx : x ∈ productSimplex (acts := acts)) :
    Proc ι acts ℝ :=
  fun d => ⟨x d, (Set.mem_pi.mp hx d (Set.mem_univ d)).1, (Set.mem_pi.mp hx d (Set.mem_univ d)).2⟩

/-- The weights of `toProcP x`. Source: none: infrastructure. Kind: L -/
@[simp] theorem toProcP_w (x : (d : ι) → acts d → ℝ) (hx : x ∈ productSimplex (acts := acts))
    (d : ι) (a : acts d) : (toProcP x hx d).w a = x d a := rfl

/-- The raw weights of the tremble `C^ε` of the procedure with raw weights `x`.
Source: [[decision-problems-v2]] Definition 10
Kind: D -/
noncomputable def trRaw (ε : ℝ) (x : (d : ι) → acts d → ℝ) : (d : ι) → acts d → ℝ :=
  fun d a => (1 - ε) * x d a + ε * (Fintype.card (acts d) : ℝ)⁻¹

/-- The tremble of `toProcP x` has raw weights `trRaw ε x`. Source: none: infrastructure. Kind: L -/
theorem tremble_toProcP_w (x : (d : ι) → acts d → ℝ) (hx : x ∈ productSimplex (acts := acts))
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (fun d => (tremble (toProcP x hx) ε h0 h1 d).w) = trRaw ε x := by
  funext d a; rfl

/-- `trRaw` is continuous in the label, coordinatewise. Source: none: infrastructure. Kind: L -/
theorem trRaw_continuous (ε : ℝ) (d : ι) (a : acts d) :
    Continuous (fun x : (d : ι) → acts d → ℝ => trRaw ε x d a) := by
  unfold trRaw
  fun_prop

/-- `rawLeafLaw` is continuous in a continuously varying weight family.
Source: none: infrastructure. Kind: L -/
theorem rawLeafLaw_continuous_of {X : Type} [TopologicalSpace X]
    (W : X → (e : ι) → acts e → ℝ) (hW : ∀ e a, Continuous (fun x => W x e a)) :
    (B : Tree Ω ι acts ℝ) → ∀ ℓ, Continuous (fun x => rawLeafLaw (W x) B ℓ)
  | .leaf _ _, _ => by simp only [rawLeafLaw]; exact continuous_const
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [rawLeafLaw]
      exact continuous_const.mul (rawLeafLaw_continuous_of W hW (child i) ℓ)
  | .decision e child, ⟨a, ℓ⟩ => by
      simp only [rawLeafLaw]
      exact (hW e a).mul (rawLeafLaw_continuous_of W hW (child a) ℓ)

/-- `ν` of a raw weight family. Source: none: infrastructure. Kind: D -/
noncomputable def rawNuP (W : (e : ι) → acts e → ℝ) (B : Tree Ω ι acts ℝ) (X : Finset Ω) : ℝ :=
  ∑ ℓ ∈ worldEv B X, rawLeafLaw W B ℓ

/-- `paySum` of a raw weight family. Source: none: infrastructure. Kind: D -/
noncomputable def rawPayP (W : (e : ι) → acts e → ℝ) (B : Tree Ω ι acts ℝ) (X : Finset Ω) : ℝ :=
  ∑ ℓ ∈ worldEv B X, rawLeafLaw W B ℓ * payoff B ℓ

/-- `ν_{C'}(X) = rawNuP` of `C'`'s weights. Source: none: infrastructure. Kind: L -/
theorem nu_eq_rawNuP (C' : Proc ι acts ℝ) (B : Tree Ω ι acts ℝ) (X : Finset Ω) :
    nu C' B X = rawNuP (fun e => (C' e).w) B X := by
  unfold nu mass rawNuP
  exact Finset.sum_congr rfl fun ℓ _ => leafLaw_eq_rawLeafLaw C' B ℓ

/-- `paySum_{C'}(X) = rawPayP` of `C'`'s weights. Source: none: infrastructure. Kind: L -/
theorem paySum_eq_rawPayP (C' : Proc ι acts ℝ) (B : Tree Ω ι acts ℝ) (X : Finset Ω) :
    paySum C' B X = rawPayP (fun e => (C' e).w) B X := by
  unfold paySum rawPayP
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw_eq_rawLeafLaw C' B ℓ]

end domain

/-! ## Realized acts and the act values -/

section values

variable (B : Tree Ω ι acts ℝ)

/-- The acts of `d` *realized within `O_d`*: some chance-positive leaf has its world in
`b ∧ O_d`. Under a full-support procedure these are exactly the acts with `ν(b ∧ O_d) > 0`.
Source: `dp-calibration` `Devices.lean` docstring ("positive iff some chance-positive leaf
satisfies `a ∧ O_d`, independently of `C`"); mandate T8(a)
Kind: D -/
noncomputable def realized (d : ι) : Finset (acts d) := by
  classical exact Finset.univ.filter fun b =>
    ∃ ℓ, 0 < chanceWeight B ℓ ∧ world B ℓ ∈ actEv d b ∩ obs d

/-- Membership in `realized`. Source: none: infrastructure. Kind: L -/
theorem mem_realized (d : ι) (b : acts d) :
    b ∈ realized obs actEv B d ↔ ∃ ℓ, 0 < chanceWeight B ℓ ∧ world B ℓ ∈ actEv d b ∩ obs d := by
  unfold realized
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Under a full-support procedure, `ν(b ∧ O_d) > 0` iff `b` is realized within `O_d`.
Source: `dp-calibration` `Devices.lean` docstring; mandate T8(a)
Kind: L -/
theorem nu_pos_iff_realized {C' : Proc ι acts ℝ} (hC : C'.FullSupport) (d : ι) (b : acts d) :
    0 < nu C' B (actEv d b ∩ obs d) ↔ b ∈ realized obs actEv B d := by
  rw [mem_realized]
  unfold nu mass
  have hnn : ∀ ℓ ∈ worldEv B (actEv d b ∩ obs d), 0 ≤ leafLaw C' B ℓ :=
    fun ℓ _ => leafLaw_nonneg C' B ℓ
  constructor
  · intro hpos
    by_contra hne
    have : ∑ ℓ ∈ worldEv B (actEv d b ∩ obs d), leafLaw C' B ℓ = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      have hw : world B ℓ ∈ actEv d b ∩ obs d := (Finset.mem_filter.mp hℓ).2
      rcases (leafLaw_nonneg C' B ℓ).lt_or_eq with hl | hl
      · exact absurd ⟨ℓ, Positive.of_leafLaw_pos C' hl, hw⟩ hne
      · exact hl.symm
    rw [this] at hpos; exact lt_irrefl _ hpos
  · rintro ⟨ℓ, hcw, hw⟩
    have hℓ : ℓ ∈ worldEv B (actEv d b ∩ obs d) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    calc (0 : ℝ) < leafLaw C' B ℓ := leafLaw_pos_of_fullSupport hC B ℓ hcw
      _ ≤ ∑ ℓ ∈ worldEv B (actEv d b ∩ obs d), leafLaw C' B ℓ :=
        Finset.single_le_sum hnn hℓ

/-- The strictly calibrated act value at the tremble, as a function of the raw label:
`𝔼_{C^ε}[r ∣ b ∧ O_d]`.
Source: `seeds.md` SE-18′(a) ("values … continuous rational functions of `C_ε`")
Kind: D -/
noncomputable def vRaw (ε : ℝ) (d : ι) (b : acts d) (x : (d : ι) → acts d → ℝ) : ℝ :=
  rawPayP (trRaw ε x) B (actEv d b ∩ obs d) / rawNuP (trRaw ε x) B (actEv d b ∩ obs d)

/-- `vRaw` is `condExp` at the tremble of `toProcP x`. Source: none: infrastructure. Kind: L -/
theorem condExp_tremble_eq_vRaw (x : (d : ι) → acts d → ℝ) (hx : x ∈ productSimplex (acts := acts))
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (d : ι) (b : acts d) :
    condExp (tremble (toProcP x hx) ε h0 h1) B (actEv d b ∩ obs d) = vRaw obs actEv B ε d b x := by
  unfold condExp vRaw
  rw [paySum_eq_rawPayP, nu_eq_rawNuP, tremble_toProcP_w]

/-- `ν` at the tremble is `rawNuP (trRaw ε x)`. Source: none: infrastructure. Kind: L -/
theorem nu_tremble_eq_rawNuP (x : (d : ι) → acts d → ℝ) (hx : x ∈ productSimplex (acts := acts))
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (X : Finset Ω) :
    nu (tremble (toProcP x hx) ε h0 h1) B X = rawNuP (trRaw ε x) B X := by
  rw [nu_eq_rawNuP, tremble_toProcP_w]

/-- `rawNuP (trRaw ε ·)` and `rawPayP (trRaw ε ·)` are continuous. Source: none: infrastructure.
Kind: L -/
theorem rawNuP_trRaw_continuous (ε : ℝ) (X : Finset Ω) :
    Continuous (fun x => rawNuP (trRaw ε x) B X) := by
  unfold rawNuP
  exact continuous_finsetSum _ fun ℓ _ =>
    rawLeafLaw_continuous_of (trRaw ε) (trRaw_continuous ε) B ℓ

/-- Continuity of the trembled payoff mass. Source: none: infrastructure. Kind: L -/
theorem rawPayP_trRaw_continuous (ε : ℝ) (X : Finset Ω) :
    Continuous (fun x => rawPayP (trRaw ε x) B X) := by
  unfold rawPayP
  exact continuous_finsetSum _ fun ℓ _ =>
    (rawLeafLaw_continuous_of (trRaw ε) (trRaw_continuous ε) B ℓ).mul continuous_const

/-- **The trembled act value of a realized act is continuous on the product simplex** (its
denominator is positive there, by full support).
Source: `seeds.md` SE-18′(a) ("`κ` is continuous … denominators bounded away from `0`")
Kind: P
Hyps: (a) `0 < ε ≤ 1`, (a) `b` realized within `O_d` -/
theorem vRaw_continuousOn (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ι) (b : acts d)
    (hb : b ∈ realized obs actEv B d) :
    ContinuousOn (vRaw obs actEv B ε d b) (productSimplex (acts := acts)) := by
  unfold vRaw
  refine ContinuousOn.div (rawPayP_trRaw_continuous B ε _).continuousOn
    (rawNuP_trRaw_continuous B ε _).continuousOn fun x hx => ?_
  rw [← nu_tremble_eq_rawNuP B x hx ε h0.le h1]
  exact ((nu_pos_iff_realized obs actEv B (tremble_fullSupport _ ε h0 h1) d b).mpr hb).ne'

end values

/-! ## The fixed-point face and Kakutani, over the queried points

Kakutani needs a compact convex subset of a *finite-dimensional* space. The point type `ι` may
be infinite, but a finite tree queries only the finite set `queried B`, and `D2At` constrains
a procedure only there; so the fixed point is taken in the product of simplices over the finite
subtype `QPt B := {d // d ∈ queried B}` and extended off the queried set by a fixed point mass
(`extQ`), which never enters the run law. This is the "`Finset` product over `queried B`" of
mandate T8, and it is what makes the discharge of `testSeq_exists_open` *exact* (the OPEN row
has no `Fintype ι`; audit round 1, B1/B2). -/

section face

variable (B : Tree Ω ι acts ℝ)

/-- The points queried in `B`, as a finite type: the coordinates of Kakutani's domain (`ι` itself
may be infinite).
Source: none: infrastructure (mandate T8's "the `Finset` product over `queried B`")
Kind: D -/
abbrev QPt : Type := {d : ι // d ∈ queried B}

/-- The product of the standard simplices over the queried points, `∏_{d ∈ queried B} Δ(A_d)`: a
compact convex subset of a finite-dimensional space, for every point type `ι`.
Source: `seeds.md` SE-18′(a) (the domain of the fixed-point map); `fix-kakutani`'s
`kakutani_pi_stdSimplex`
Kind: D -/
def productSimplexQ : Set ((q : QPt B) → acts q.1 → ℝ) :=
  Set.univ.pi fun q => stdSimplex ℝ (acts q.1)

/-- Extension of a queried-point label to all of `ι`: the given label at queried points, a fixed
point mass elsewhere (unqueried points never enter the run law, `leafLaw_congr_queried`).
Source: none: infrastructure
Kind: D -/
noncomputable def extQ (y : (q : QPt B) → acts q.1 → ℝ) : (d : ι) → acts d → ℝ :=
  fun d => if h : d ∈ queried B then y ⟨d, h⟩ else Pi.single (Classical.arbitrary (acts d)) 1

/-- `extQ` at a queried point. Source: none: infrastructure. Kind: L -/
theorem extQ_of_mem (y : (q : QPt B) → acts q.1 → ℝ) {d : ι} (hd : d ∈ queried B) :
    extQ B y d = y ⟨d, hd⟩ := by
  unfold extQ; exact dif_pos hd

/-- `extQ` at an unqueried point. Source: none: infrastructure. Kind: L -/
theorem extQ_of_not_mem (y : (q : QPt B) → acts q.1 → ℝ) {d : ι} (hd : d ∉ queried B) :
    extQ B y d = Pi.single (Classical.arbitrary (acts d)) 1 := by
  unfold extQ; exact dif_neg hd

/-- `extQ` maps the queried-point product simplex into the full one.
Source: none: infrastructure. Kind: L -/
theorem extQ_mem {y : (q : QPt B) → acts q.1 → ℝ} (hy : y ∈ productSimplexQ B) :
    extQ B y ∈ productSimplex (acts := acts) := by
  refine Set.mem_pi.mpr fun d _ => ?_
  by_cases hd : d ∈ queried B
  · rw [extQ_of_mem B y hd]; exact Set.mem_pi.mp hy ⟨d, hd⟩ (Set.mem_univ _)
  · rw [extQ_of_not_mem B y hd]; exact single_mem_stdSimplex ℝ _

/-- `extQ` is continuous (each coordinate is a projection or a constant).
Source: none: infrastructure. Kind: L -/
theorem extQ_continuous : Continuous (extQ B (acts := acts)) := by
  refine continuous_pi fun d => ?_
  by_cases hd : d ∈ queried B
  · have h : (fun y : (q : QPt B) → acts q.1 → ℝ => extQ B y d) = fun y => y ⟨d, hd⟩ :=
      funext fun y => extQ_of_mem B y hd
    rw [h]; exact continuous_apply _
  · have h : (fun y : (q : QPt B) → acts q.1 → ℝ => extQ B y d) =
        fun _ => Pi.single (Classical.arbitrary (acts d)) 1 :=
      funext fun y => extQ_of_not_mem B y hd
    rw [h]; exact continuous_const

/-- **The fixed-point face `Φ_ε(y)`** over the queried points: the queried-point labels that, at
every queried `d` with a realized act, put weight only on realized acts maximising
`vRaw ε d · (extQ y)` over the realized acts (Definition 18's escape clause: no constraint where
no act is realized within `O_d`).
Source: `seeds.md` SE-18′(a) (`Φ_ε`); [[decision-problems-v2]] §4 Definition 18; `dp-calibration`
`D2At`
Kind: D
Fidelity: variant: no ε-floor — the face is taken in D2At's own form (values at `C'^ε`, support
of `C'`), which is what the fixed point must satisfy; indexed by the queried points so that `ι`
is arbitrary -/
def fpFace (ε : ℝ) (y : (q : QPt B) → acts q.1 → ℝ) : Set ((q : QPt B) → acts q.1 → ℝ) :=
  {z | z ∈ productSimplexQ B ∧
    ∀ q : QPt B, (realized obs actEv B q.1).Nonempty → ∀ a, 0 < z q a →
      a ∈ realized obs actEv B q.1 ∧
      ∀ b ∈ realized obs actEv B q.1,
        vRaw obs actEv B ε q.1 b (extQ B y) ≤ vRaw obs actEv B ε q.1 a (extQ B y)}

/-- `fpFace` maps into the queried-point product simplex. Source: none: infrastructure. Kind: L -/
theorem fpFace_maps (ε : ℝ) :
    ∀ y ∈ productSimplexQ B, fpFace obs actEv B ε y ⊆ productSimplexQ B :=
  fun _ _ _ hz => hz.1

/-- `fpFace ε y` is nonempty: at each queried `d`, a point mass on a realized maximiser (or
anywhere when no act is realized).
Source: `seeds.md` SE-18′(a) ("nonempty"); `dp-calibration` `Devices.lean` ("nonempty precisely
because of the escape clause")
Kind: L -/
theorem fpFace_nonempty (ε : ℝ) :
    ∀ y ∈ productSimplexQ B, (fpFace obs actEv B ε y).Nonempty := by
  classical
  intro y _
  -- choose a maximiser at each queried `d` (or an arbitrary act)
  have hsel : ∀ q : QPt B, ∃ a : acts q.1, (realized obs actEv B q.1).Nonempty →
      a ∈ realized obs actEv B q.1 ∧
      ∀ b ∈ realized obs actEv B q.1,
        vRaw obs actEv B ε q.1 b (extQ B y) ≤ vRaw obs actEv B ε q.1 a (extQ B y) := by
    intro q
    by_cases hne : (realized obs actEv B q.1).Nonempty
    · obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_max_image (realized obs actEv B q.1)
        (fun a => vRaw obs actEv B ε q.1 a (extQ B y)) hne
      exact ⟨a₀, fun _ => ⟨ha₀, hmax⟩⟩
    · exact ⟨Classical.arbitrary _, fun h => absurd h hne⟩
  choose sel hsel using hsel
  refine ⟨fun q => Pi.single (sel q) 1, ?_, ?_⟩
  · exact Set.mem_pi.mpr fun q _ => single_mem_stdSimplex ℝ (sel q)
  · intro q hne a ha
    have ha' : 0 < (Pi.single (sel q) (1 : ℝ) : acts q.1 → ℝ) a := ha
    have : a = sel q := by
      by_contra hne'
      rw [Pi.single_apply, if_neg hne'] at ha'
      exact lt_irrefl _ ha'
    subst this
    exact hsel q hne

/-- `fpFace ε y` is convex (a product of faces).
Source: `seeds.md` SE-18′(a) ("convex"). Kind: L -/
theorem fpFace_convex (ε : ℝ) :
    ∀ y ∈ productSimplexQ B, Convex ℝ (fpFace obs actEv B ε y) := by
  intro y _ z hz w hw s t hs ht hst
  refine ⟨?_, fun q hne a ha => ?_⟩
  · exact (convex_pi fun q _ => convex_stdSimplex ℝ (acts q.1)) hz.1 hw.1 hs ht hst
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha
    have hz0 := (Set.mem_pi.mp hz.1 q (Set.mem_univ q)).1 a
    have hw0 := (Set.mem_pi.mp hw.1 q (Set.mem_univ q)).1 a
    by_cases hza : 0 < z q a
    · exact hz.2 q hne a hza
    · have hza' : z q a = 0 := le_antisymm (not_lt.mp hza) hz0
      have hwa : 0 < w q a := by
        by_contra hc
        have hwa' : w q a = 0 := le_antisymm (not_lt.mp hc) hw0
        rw [hza', hwa'] at ha; simp at ha
      exact hw.2 q hne a hwa

/-- The queried-point product simplex is closed. Source: none: infrastructure. Kind: L -/
theorem isClosed_productSimplexQ : IsClosed (productSimplexQ B) :=
  isClosed_set_pi fun q _ => isClosed_stdSimplex ℝ (acts q.1)

/-- The full product simplex is closed. Source: none: infrastructure. Kind: L -/
theorem isClosed_productSimplex : IsClosed (productSimplex (acts := acts)) :=
  isClosed_set_pi fun d _ => isClosed_stdSimplex ℝ (acts d)

/-- **The graph of `fpFace ε` over the queried-point product simplex is closed** (sequential
criterion; a supported act stays supported along a tail, where it is a realized maximiser; weak
inequalities pass to the limit by `vRaw_continuousOn` composed with the continuous `extQ`).
Source: `seeds.md` SE-18′(a) ("closed graph"); mandate T8(a) ("closed graph (prove)")
Kind: P
Hyps: (a) `0 < ε ≤ 1` -/
theorem fpFace_hasClosedGraphOn (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    HasClosedGraphOn (fpFace obs actEv B ε) (productSimplexQ B) := by
  rw [hasClosedGraphOn_iff_seq_of_isClosed (isClosed_productSimplexQ B)]
  intro ys zs y z hmem hys hzs
  have hyK : y ∈ productSimplexQ B :=
    (isClosed_productSimplexQ B).mem_of_tendsto hys (Eventually.of_forall fun n => (hmem n).1)
  have hzK : z ∈ productSimplexQ B :=
    (isClosed_productSimplexQ B).mem_of_tendsto hzs (Eventually.of_forall fun n => (hmem n).2.1)
  refine ⟨hzK, fun q hne a ha => ?_⟩
  -- the extended labels converge within the full product simplex
  have hext : Tendsto (fun n => extQ B (ys n)) atTop
      (𝓝[productSimplex (acts := acts)] (extQ B y)) :=
    tendsto_nhdsWithin_iff.2 ⟨((extQ_continuous B).tendsto y).comp hys,
      Eventually.of_forall fun n => extQ_mem B (hmem n).1⟩
  have hconv : ∀ c ∈ realized obs actEv B q.1,
      Tendsto (fun n => vRaw obs actEv B ε q.1 c (extQ B (ys n))) atTop
        (𝓝 (vRaw obs actEv B ε q.1 c (extQ B y))) :=
    fun c hc => ((vRaw_continuousOn obs actEv B ε h0 h1 q.1 c hc).continuousWithinAt
      (extQ_mem B hyK)).tendsto.comp hext
  have hza : Tendsto (fun n => zs n q a) atTop (𝓝 (z q a)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hzs q) a
  have hev : ∀ᶠ n in atTop, 0 < zs n q a := hza.eventually (lt_mem_nhds ha)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hreal : a ∈ realized obs actEv B q.1 := ((hmem N).2.2 q hne a (hN N le_rfl)).1
  refine ⟨hreal, fun b hb => ?_⟩
  refine le_of_tendsto_of_tendsto (hconv b hb) (hconv a hreal) ?_
  filter_upwards [hev] with n hn
  exact ((hmem n).2.2 q hne a hn).2 b hb

/-- Per-`ε` fixed points as queried-point labels (the form compactness needs): Kakutani on
`fpFace ε` over `productSimplexQ`, the fixed point extended by `extQ` and read as a procedure.
Source: none: infrastructure. Kind: L -/
theorem fixedPoint_exists (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∃ y, ∃ hy : y ∈ productSimplexQ B,
      D2At obs actEv B (toProcP (extQ B y) (extQ_mem B hy)) ε h0 h1 := by
  obtain ⟨y, hyK, hyF⟩ := kakutani_pi_stdSimplex (A := fun q : QPt B => acts q.1)
    (fpFace obs actEv B ε) (fpFace_maps obs actEv B ε) (fpFace_nonempty obs actEv B ε)
    (fpFace_convex obs actEv B ε) (fpFace_hasClosedGraphOn obs actEv B ε h0 h1)
  refine ⟨y, hyK, ?_⟩
  intro d hd _ hb a ha
  have hfs := tremble_fullSupport (toProcP (extQ B y) (extQ_mem B hyK)) ε h0 h1
  obtain ⟨b, hb⟩ := hb
  have hbr : b ∈ realized obs actEv B d := (nu_pos_iff_realized obs actEv B hfs d b).mp hb
  have ha' : 0 < y ⟨d, hd⟩ a := by
    rw [toProcP_w, extQ_of_mem B y hd] at ha; exact ha
  obtain ⟨har, hmax⟩ := hyF.2 ⟨d, hd⟩ ⟨b, hbr⟩ a ha'
  refine ⟨(nu_pos_iff_realized obs actEv B hfs d a).mpr har, fun c hc => ?_⟩
  rw [condExp_tremble_eq_vRaw, condExp_tremble_eq_vRaw]
  exact hmax c ((nu_pos_iff_realized obs actEv B hfs d c).mp hc)

/-- **T8(a): for every `ε ∈ (0, 1]` some procedure satisfies `D2At` at `ε`** — an
ε-calibrated-and-approved procedure, by `kakutani_pi_stdSimplex` on `fpFace ε` over the queried
points (nonempty convex values, closed graph proved), for every point type `ι`. SE-18′(a) with
its hypotheses discharged: no recording and no realizability of `O_d` is needed, because the
escape clause of D2At handles points where no act is realized within `O_d`.
Source: `cf-workflow/phase2-notes/repair/seeds.md` SE-18′(a); `dp-calibration` `Devices.lean`
(the route sketched for `testSeq_exists_open`); mandate T8(a)
Kind: C
Fidelity: stronger: SE-18′(a) assumes recording at the queried points and realized observations
under full-support procedures; neither is needed in the D2At form. No finiteness of `ι` is
assumed (the tree is finite, so `queried B` is).
Hyps: (a) `0 < ε ≤ 1` -/
theorem d2At_exists (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∃ C' : Proc ι acts ℝ, D2At obs actEv B C' ε h0 h1 := by
  obtain ⟨y, hy, hD⟩ := fixedPoint_exists obs actEv B ε h0 h1
  exact ⟨toProcP (extQ B y) (extQ_mem B hy), hD⟩

end face

/-! ## The discharge: a convergent subsequence of fixed points -/

section discharge

variable (B : Tree Ω ι acts ℝ)

/-- `1/(n+2) ∈ (0, 1]`. Source: none: infrastructure. Kind: L -/
theorem epsSeq_mem (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 2) ∧ (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **T8(b): `testSeq_exists` — on every finite tree over `ℝ`, for every point type `ι`, some
procedure is test-sequence tremble-EDT-consistent.** `ε_n := 1/(n+2)`; `y_n` the per-`ε_n` fixed
point of `fixedPoint_exists` in the queried-point product simplex; a subsequence converges there
by compactness (`IsCompact.tendsto_subseq`); its limit `y`, extended by `extQ` and read as a
procedure, with the subsequence `(ε_{φ n}, extQ y_{φ n})`, witnesses `TestSeqTrembleEdtConsistent`
(the weights converge at every point of `ι`: at queried points by the subsequence, elsewhere
because both sides are the same constant). This is `dp-calibration`'s OPEN row
`testSeq_exists_open` without its unused `_hpruned` hypothesis.
Source: `cf-workflow/phase2-notes/repair/dynamic.md` DY-3 ("Existence on every finite tree");
`dp-calibration` `Devices.lean` `testSeq_exists_open` (OPEN row, discharged here); mandate T8(b)
Kind: C
Fidelity: stronger: no pruned-chance hypothesis (the OPEN row's docstring says it is unused)
Hyps: (a) none beyond the tree being finite and the action sets nonempty -/
theorem testSeq_exists (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) :
    ∃ C : Proc ι acts ℝ, TestSeqTrembleEdtConsistent obs actEv C B := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hε : ∀ n, 0 < ε n ∧ ε n ≤ 1 := fun n => epsSeq_mem n
  have hfp : ∀ n, ∃ y, ∃ hy : y ∈ productSimplexQ B,
      D2At obs actEv B (toProcP (extQ B y) (extQ_mem B hy)) (ε n) (hε n).1 (hε n).2 :=
    fun n => fixedPoint_exists obs actEv B (ε n) (hε n).1 (hε n).2
  choose ys hys hD using hfp
  have hcomp : IsCompact (productSimplexQ B) :=
    isCompact_univ_pi fun q => isCompact_stdSimplex ℝ (acts q.1)
  obtain ⟨y, hyK, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hys
  refine ⟨toProcP (extQ B y) (extQ_mem B hyK), fun n => ε (φ n),
    fun n => toProcP (extQ B (ys (φ n))) (extQ_mem B (hys (φ n))),
    fun n => hε (φ n), ?_, ?_, fun n => hD (φ n)⟩
  · -- `ε (φ n) → 0`
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    show 1 / ((φ n : ℝ) + 2) < δ
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  · -- pointwise convergence of the weights, through the continuous extension
    intro d a δ hδ
    have hext : Tendsto (fun n => extQ B (ys (φ n))) atTop (𝓝 (extQ B y)) :=
      ((extQ_continuous B).tendsto y).comp hlim
    have h1 : Tendsto (fun n => extQ B (ys (φ n)) d a) atTop (𝓝 (extQ B y d a)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hext d) a
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h1 δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq] at this
    simpa using this

end discharge

/-- **`testSeq_exists_open`, discharged**: exactly `dp-calibration`'s OPEN statement — same
instance arguments (no `Fintype ι`), same explicit-argument order `(obs) (actEv) (B) (_hpruned)`,
the unused pruned-chance hypothesis present — so the two signatures are syntactically comparable
(`#check` both). `dp-calibration`'s file is frozen and cannot import this package; the
orchestrator closes the row at consolidation.
Source: `dp-calibration` `Devices.lean` line 75 (`testSeq_exists_open`); mandate T8(b)
Kind: C
Fidelity: exact
Hyps: (a) none used (`_hpruned` unused, as in the OPEN row) -/
theorem testSeq_exists_open_discharged (obs : ι → Finset Ω)
    (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℝ)
    (_hpruned : ∀ ℓ, 0 < chanceWeight B ℓ) :
    ∃ C : Proc ι acts ℝ, TestSeqTrembleEdtConsistent obs actEv C B :=
  testSeq_exists B obs actEv

end Cleanroom.Decision.DpDutchBook
