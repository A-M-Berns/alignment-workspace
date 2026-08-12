/-
==============================================================================
TTTransitivity.lean — run3 TODO 4 (`tt-transitivity-forall`)

First kernel-checked cross-agent Total-Trust statement: NON-TRANSITIVITY of
DDB / LeanDeference Total Trust with the honest `∀ X ∀ s` quantifier.

STANDALONE file (GROUND-RULES §2: no `import LeanDeference`).  The Total-Trust
predicate `TT` below is the STATEMENT FORM of the conditional-mass inequality
certified by `DeferenceConverse.value_witness_iff_totalTrust_mass`
(lean-deference/LeanDeference.lean, lines 426–431), copied with
citation.  The glue lemma `tt_mass_nonneg_iff` restates the
`totalTrust_sum_split` algebra (ibid. lines 395–431) for a generic linearly
ordered field; it is COPIED GLUE, not a contribution.  Nothing about Value or
the Value⟺TT equivalence is (re-)proved here.

Contents:
  1. `TT_condExpert` (reusable lemma): the π-conditional-expectation expert of
     ANY partition (fibers of any map `c : W → ι`) is Totally Trusted by its
     own prior π — for ALL `X : W → F` and ALL `s : F`.  Classical mathematics
     (the finite law of total expectation read as a Total-Trust statement);
     labeled as instantiation, not discovery.
  2. The concrete Fin-3 chain: `link1 : TT πH PA`, `link2 : TT πA PB` (both by
     lemma 1, hence with the genuine ∀X∀s quantifier), and
     `long_edge_fails : ¬ TT πH PB` at the explicit witness
     X = 1[world 1], s = 1/2, with the kernel-checked exact gap 1/8
     (`long_edge_gap`).
  3. Recovery near-miss: `recovery : TT πH PB'` where PB' is the SAME
     partition F_B conditioned by πH instead of πA — the failure is caused by
     the prior mismatch, not by the frame.
  4. Non-degeneracy: `priors_differ`, `PB_not_piH_conditional`,
     partition non-triviality, rows-sum-to-1, priors-sum-to-1.
  5. (Beyond the mandatory clauses) the exact characterization:
     `TT_condExpert_cross_iff` — for positive priors,
     `TT πH (condExpert πA c) ↔ πA(·|C) = πH(·|C) on every fiber C of c`.
     Its instantiation `sharper_recovery` shows prior IDENTITY is sufficient
     but not necessary (differing priors with cellwise-equal conditionals).

HONEST SCOPE: a finite-frame DDB statement over an ordered field — the first
machine-checked statement in this lab whose SUBJECT is trust between two
agents with the genuine `∀X ∀s` quantifier.  It is NOT an LI/asymptotic
result; nothing here touches logical inductors.

Relation to `DeferenceExtra.CM_implies_immodest` (LeanDeference.lean L248):
non-overlapping.  That theorem assumes the conditional-martingale IDENTITY at
a world and concludes fiber-mass collapse (immodesty); lemma 1 here goes the
other way around a different square: partition-conditional FORM of the expert
⇒ the Total-Trust INEQUALITY for all X, s.  Neither statement implies the
other's hypotheses or conclusion.

SUPERSESSION: run2/work/trust-laundering.{py,md} is POISONED (verdict SHADOW);
none of its numbers are cited; the companion tt_search.py re-derives
everything with an exact (grid-free) decision procedure.
==============================================================================
-/
import Mathlib

set_option linter.unusedSectionVars false

open Finset

namespace TTTrans

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Total Trust** (DDB conditional-mass form), quantified over ALL test
variables `X` and thresholds `s`.  Statement form copied with citation from
`DeferenceConverse.value_witness_iff_totalTrust_mass`
(LeanDeference.lean L426–431). -/
def TT (π : W → F) (P : W → W → F) : Prop :=
  ∀ (X : W → F) (s : F),
    s * (∑ w, if s ≤ ∑ v, P w v * X v then π w else 0)
      ≤ ∑ w, if s ≤ ∑ v, P w v * X v then π w * X w else 0

/-- Glue identity (the `totalTrust_sum_split` algebra of LeanDeference.lean
L395–431, restated for a generic ordered field because GROUND-RULES §2 forbids
importing the corpus): the TT inequality at `(X,s)` is equivalent to
nonnegativity of the TT mass `∑_{E_w(X) ≥ s} π_w (X_w − s)`.  Copied glue, not
a contribution. -/
theorem tt_mass_nonneg_iff (π : W → F) (P : W → W → F) (X : W → F) (s : F) :
    (s * (∑ w, if s ≤ ∑ v, P w v * X v then π w else 0)
      ≤ ∑ w, if s ≤ ∑ v, P w v * X v then π w * X w else 0)
    ↔ 0 ≤ ∑ w, if s ≤ ∑ v, P w v * X v then π w * (X w - s) else 0 := by
  rw [← sub_nonneg]
  have hsplit :
      (∑ w, if s ≤ ∑ v, P w v * X v then π w * X w else 0)
        - s * (∑ w, if s ≤ ∑ v, P w v * X v then π w else 0)
      = ∑ w, if s ≤ ∑ v, P w v * X v then π w * (X w - s) else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : s ≤ ∑ v, P w v * X v
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  rw [hsplit]

/-! ## Partition conditional-expectation experts -/

/-- π-mass of the `c`-fiber labeled `r`. -/
def fiberMass (π : W → F) (c : W → ι) (r : ι) : F :=
  ∑ u, if c u = r then π u else 0

/-- π-weighted sum of `X` over the `c`-fiber labeled `r`. -/
def fiberSum (π : W → F) (c : W → ι) (X : W → F) (r : ι) : F :=
  ∑ v, if c v = r then π v * X v else 0

/-- The `π`-conditional-expectation expert of the fiber partition of `c`:
row `w` is `π` conditioned on the cell `{v : c v = c w}`. -/
def condExpert (π : W → F) (c : W → ι) : W → W → F :=
  fun w v => (if c v = c w then π v else 0) / fiberMass π c (c w)

lemma fiberMass_pos (π : W → F) (c : W → ι) (hπ : ∀ w, 0 < π w) (w0 : W) :
    0 < fiberMass π c (c w0) := by
  refine Finset.sum_pos' (fun u _ => ?_) ⟨w0, Finset.mem_univ w0, ?_⟩
  · by_cases h : c u = c w0 <;> simp [h, (hπ u).le]
  · simpa using hπ w0

/-- The expert's estimate is the fiber conditional expectation. -/
lemma condExpert_E (π : W → F) (c : W → ι) (X : W → F) (w : W) :
    (∑ v, condExpert π c w v * X v)
      = fiberSum π c X (c w) / fiberMass π c (c w) := by
  simp only [fiberSum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases h : c v = c w <;> simp [condExpert, h, div_mul_eq_mul_div]

/-- Regroup a sum over worlds into fibers of `c` (empty fibers contribute 0). -/
lemma sum_fiber (f : W → F) (c : W → ι) :
    (∑ w, f w) = ∑ r : ι, ∑ w, if c w = r then f w else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

/-- Split a fiber-restricted mass term. -/
lemma fiber_split (π : W → F) (c : W → ι) (X : W → F) (s : F) (r : ι) :
    (∑ w, if c w = r then π w * (X w - s) else 0)
      = fiberSum π c X r - s * fiberMass π c r := by
  simp only [fiberSum, fiberMass]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : c w = r
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- **Reusable lemma 1 (the engine).**  A partition conditional-expectation
expert is Totally Trusted by its own prior, for ALL `X` and `s`.  This is the
finite law of total expectation read as a Total-Trust statement: the event
`{E(X) ≥ s}` is a union of fibers, and each fiber contributes
`π(fiber)·(E_fiber(X) − s) ≥ 0`.  Classical; labeled instantiation. -/
theorem TT_condExpert (π : W → F) (c : W → ι) (hπ : ∀ w, 0 < π w) :
    TT π (condExpert π c) := by
  intro X s
  rw [tt_mass_nonneg_iff]
  have hE : ∀ w, (∑ v, condExpert π c w v * X v)
      = fiberSum π c X (c w) / fiberMass π c (c w) := condExpert_E π c X
  simp only [hE]
  rw [sum_fiber
    (fun w => if s ≤ fiberSum π c X (c w) / fiberMass π c (c w)
              then π w * (X w - s) else 0) c]
  refine Finset.sum_nonneg (fun r _ => ?_)
  have hcongr :
      (∑ w, if c w = r then
          (if s ≤ fiberSum π c X (c w) / fiberMass π c (c w)
           then π w * (X w - s) else 0) else 0)
      = ∑ w, if c w = r then
          (if s ≤ fiberSum π c X r / fiberMass π c r
           then π w * (X w - s) else 0) else 0 := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : c w = r
    · rw [h]
    · simp [h]
  rw [hcongr]
  by_cases hsr : s ≤ fiberSum π c X r / fiberMass π c r
  · simp only [if_pos hsr]
    rw [fiber_split]
    by_cases hem : ∃ w0, c w0 = r
    · obtain ⟨w0, hw0⟩ := hem
      have hMpos : 0 < fiberMass π c r := hw0 ▸ fiberMass_pos π c hπ w0
      have h1 : s * fiberMass π c r ≤ fiberSum π c X r :=
        (le_div_iff₀ hMpos).mp hsr
      linarith
    · push_neg at hem
      have hS0 : fiberSum π c X r = 0 := by
        simp only [fiberSum]
        exact Finset.sum_eq_zero (fun v _ => by rw [if_neg (hem v)])
      have hM0 : fiberMass π c r = 0 := by
        simp only [fiberMass]
        exact Finset.sum_eq_zero (fun u _ => by rw [if_neg (hem u)])
      rw [hS0, hM0]
      simp
  · simp only [if_neg hsr]
    simp

/-! ## The concrete chain (worlds `Fin 3`, rationals) -/

/-- Human prior `(1/2, 1/4, 1/4)`. -/
def πH : Fin 3 → ℚ := fun w => if w = 0 then 1/2 else 1/4
/-- Advisor prior `(1/4, 1/2, 1/4)` — differs from `πH`. -/
def πA : Fin 3 → ℚ := fun w => if w = 1 then 1/2 else 1/4
/-- Partition `F_A`: cells `{0}`, `{1,2}` (fibers of `cA`). -/
def cA : Fin 3 → Fin 3 := fun w => if w = 0 then 0 else 1
/-- Partition `F_B`: cells `{0,1}`, `{2}` (fibers of `cB`). -/
def cB : Fin 3 → Fin 3 := fun w => if w = 2 then 2 else 0

/-- Expert A: `πH`-conditional on `F_A` = `[[1,0,0],[0,1/2,1/2],[0,1/2,1/2]]`. -/
def PA : Fin 3 → Fin 3 → ℚ := condExpert πH cA
/-- Expert B: `πA`-conditional on `F_B` = `[[1/3,2/3,0],[1/3,2/3,0],[0,0,1]]`.
NOT `πH`-conditional (see `PB_not_piH_conditional`). -/
def PB : Fin 3 → Fin 3 → ℚ := condExpert πA cB
/-- Recovery expert: the SAME partition `F_B`, conditioned by `πH` instead:
`[[2/3,1/3,0],[2/3,1/3,0],[0,0,1]]`. -/
def PB' : Fin 3 → Fin 3 → ℚ := condExpert πH cB

lemma hπH : ∀ w, 0 < πH w := by intro w; fin_cases w <;> norm_num [πH]
lemma hπA : ∀ w, 0 < πA w := by intro w; fin_cases w <;> norm_num [πA]

/-- **Link 1** — `πH` Totally Trusts `P_A`, for ALL `X : Fin 3 → ℚ`, `s : ℚ`. -/
theorem link1 : TT πH PA := TT_condExpert πH cA hπH

/-- **Link 2** — `πA` Totally Trusts `P_B`, for ALL `X : Fin 3 → ℚ`, `s : ℚ`. -/
theorem link2 : TT πA PB := TT_condExpert πA cB hπA

/-- The long-edge witness: `X = 1[world 1]`. -/
def X₀ : Fin 3 → ℚ := fun w => if w = 1 then 1 else 0

/-- **The exact gap.**  At `(X₀, 1/2)` the long-edge TT inequality fails by
exactly `1/8`:  `s·πH{E_B(X₀) ≥ s} = 3/8` versus `E_πH(X₀·1[E_B(X₀) ≥ s]) = 1/4`. -/
theorem long_edge_gap :
    (1/2 : ℚ) * (∑ w, if (1/2 : ℚ) ≤ ∑ v, PB w v * X₀ v then πH w else 0)
      - (∑ w, if (1/2 : ℚ) ≤ ∑ v, PB w v * X₀ v then πH w * X₀ w else 0)
    = 1/8 := by
  norm_num [PB, condExpert, fiberMass, πH, πA, cB, X₀, Fin.sum_univ_three]

/-- **The long edge fails**: `πH` does NOT Totally Trust `P_B`. -/
theorem long_edge_fails : ¬ TT πH PB := by
  intro h
  have h1 := h X₀ (1/2)
  have h2 := long_edge_gap
  linarith

/-- **Non-transitivity, packaged**: both short links hold with the genuine
`∀X ∀s` quantifier (they are theorems, not grid checks), yet the long edge
fails.  Total Trust does not compose across a different intermediate prior. -/
theorem TT_not_transitive : TT πH PA ∧ TT πA PB ∧ ¬ TT πH PB :=
  ⟨link1, link2, long_edge_fails⟩

/-- **Recovery near-miss (mandatory).**  Conditioning the SAME partition `F_B`
by `πH` instead of `πA` makes the long edge HOLD (for all `X, s`): the failure
is caused by the prior mismatch, not by the frame. -/
theorem recovery : TT πH PB' := TT_condExpert πH cB hπH

/-- The recovery edge holds in particular at the very witness that broke the
long edge. -/
example : (1/2 : ℚ) * (∑ w, if (1/2 : ℚ) ≤ ∑ v, PB' w v * X₀ v then πH w else 0)
    ≤ ∑ w, if (1/2 : ℚ) ≤ ∑ v, PB' w v * X₀ v then πH w * X₀ w else 0 :=
  recovery X₀ (1/2)

/-! ## Non-degeneracy checks -/

/-- The two priors genuinely differ. -/
theorem priors_differ : πA ≠ πH := by
  intro h
  have h0 := congrFun h 0
  norm_num [πA, πH] at h0

/-- `P_B` is genuinely `πA`-conditional and NOT `πH`-conditional on `F_B`
(entry `(0,1)`: `2/3 ≠ 1/3`) — guards SHADOW case (c). -/
theorem PB_not_piH_conditional : PB ≠ PB' := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [PB, PB', condExpert, fiberMass, πA, πH, cB, Fin.sum_univ_three] at h01

/-- `F_A` is a non-trivial partition: not indiscrete (`cA 0 ≠ cA 1`) and not
discrete (`cA 1 = cA 2`). -/
theorem cA_nontrivial : cA 0 ≠ cA 1 ∧ cA 1 = cA 2 := by
  constructor <;> decide

/-- `F_B` is a non-trivial partition: `cB 0 = cB 1` and `cB 1 ≠ cB 2`. -/
theorem cB_nontrivial : cB 0 = cB 1 ∧ cB 1 ≠ cB 2 := by
  constructor <;> decide

/-- The partitions genuinely differ (as fiber partitions): worlds 1 and 2 are
`F_A`-equivalent but not `F_B`-equivalent. -/
theorem partitions_differ : cA 1 = cA 2 ∧ cB 1 ≠ cB 2 :=
  ⟨cA_nontrivial.2, cB_nontrivial.2⟩

/-- Both priors are probability vectors. -/
theorem priors_sum_one : (∑ w, πH w) = 1 ∧ (∑ w, πA w) = 1 := by
  constructor <;> norm_num [πH, πA, Fin.sum_univ_three]

/-- All three experts are row-stochastic (genuine credence kernels). -/
theorem experts_row_stochastic :
    (∀ w, (∑ v, PA w v) = 1) ∧ (∀ w, (∑ v, PB w v) = 1)
      ∧ (∀ w, (∑ v, PB' w v) = 1) := by
  refine ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩ <;> fin_cases w <;>
    norm_num [PA, PB, PB', condExpert, fiberMass, πH, πA, cA, cB,
      Fin.sum_univ_three]

/-! ## The exact characterization (beyond the mandatory clauses)

For positive priors, cross-prior Total Trust in a partition expert is
EXACTLY cellwise conditional agreement.  This subsumes the recovery near-miss
(prior identity ⇒ agreement) and shows the failure's true lever: it is NOT
prior identity per se (see `sharper_recovery`), and the partition `F_A` of the
first expert is irrelevant to the long edge. -/

/-- π-weighted indicator sums over a fiber pick out single worlds. -/
lemma fiberSum_indicator (π : W → F) (c : W → ι) (v0 : W) (r : ι) :
    fiberSum π c (fun v => if v = v0 then 1 else 0) r
      = if c v0 = r then π v0 else 0 := by
  simp only [fiberSum]
  rw [Finset.sum_eq_single v0]
  · by_cases h0 : c v0 = r <;> simp [h0]
  · intro v _ hv
    by_cases h0 : c v = r <;> simp [h0, hv]
  · intro habs
    exact absurd (Finset.mem_univ v0) habs

/-- **Mismatch direction.**  If some world's conditional probability is
strictly larger under `πA` than under `πH` (within its own fiber), then `πH`
does NOT Totally Trust the `πA`-conditional expert.  Witness: `X` = that
world's indicator, `s` = its `πA`-conditional probability. -/
theorem TT_fails_of_cond_mismatch (πH' πA' : W → F) (c : W → ι)
    (hπH' : ∀ w, 0 < πH' w) (hπA' : ∀ w, 0 < πA' w) (v0 : W)
    (hmis : πH' v0 / fiberMass πH' c (c v0)
              < πA' v0 / fiberMass πA' c (c v0)) :
    ¬ TT πH' (condExpert πA' c) := by
  intro h
  have hMA : 0 < fiberMass πA' c (c v0) := fiberMass_pos πA' c hπA' v0
  have hMH : 0 < fiberMass πH' c (c v0) := fiberMass_pos πH' c hπH' v0
  have hspos : 0 < πA' v0 / fiberMass πA' c (c v0) := div_pos (hπA' v0) hMA
  have h1 := (tt_mass_nonneg_iff πH' (condExpert πA' c)
      (fun v => if v = v0 then 1 else 0)
      (πA' v0 / fiberMass πA' c (c v0))).mp
    (h (fun v => if v = v0 then 1 else 0) (πA' v0 / fiberMass πA' c (c v0)))
  -- Evaluate the expert's estimate on the indicator.
  have hE : ∀ w, (∑ v, condExpert πA' c w v * (if v = v0 then (1 : F) else 0))
      = (if c v0 = c w then πA' v0 else 0) / fiberMass πA' c (c w) := by
    intro w
    rw [condExpert_E, fiberSum_indicator]
  rw [show (∑ w, if (πA' v0 / fiberMass πA' c (c v0)) ≤
        ∑ v, condExpert πA' c w v * (if v = v0 then (1 : F) else 0)
      then πH' w * ((if w = v0 then (1 : F) else 0)
                      - πA' v0 / fiberMass πA' c (c v0)) else 0)
      = ∑ w, if c w = c v0
      then πH' w * ((if w = v0 then (1 : F) else 0)
                      - πA' v0 / fiberMass πA' c (c v0)) else 0 from ?_] at h1
  · rw [fiber_split, fiberSum_indicator, if_pos rfl] at h1
    -- h1 : 0 ≤ πH' v0 − s · fiberMass πH' c (c v0), i.e. s ≤ πH'(v0 | fiber)
    have h2 : πA' v0 / fiberMass πA' c (c v0)
        ≤ πH' v0 / fiberMass πH' c (c v0) :=
      (le_div_iff₀ hMH).mpr (by linarith)
    exact absurd h2 (not_le.mpr hmis)
  · -- the event {E ≥ s} is exactly the fiber of v0
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [hE w]
    by_cases hcw : c w = c v0
    · have heq : (if c v0 = c w then πA' v0 else 0) / fiberMass πA' c (c w)
          = πA' v0 / fiberMass πA' c (c v0) := by
        rw [hcw, if_pos rfl]
      rw [heq, if_pos le_rfl, if_pos hcw]
    · have heq : (if c v0 = c w then πA' v0 else 0) / fiberMass πA' c (c w)
          = 0 := by
        rw [if_neg (fun hh => hcw hh.symm), zero_div]
      rw [heq, if_neg (not_le.mpr hspos), if_neg hcw]

/-- **Agreement direction.**  If the two priors' conditional probabilities
agree at every world (within its own fiber), the two conditional experts are
EQUAL, hence cross-prior Total Trust holds by lemma 1. -/
theorem condExpert_eq_of_cond_agree (πH' πA' : W → F) (c : W → ι)
    (hagree : ∀ v, πA' v / fiberMass πA' c (c v)
                     = πH' v / fiberMass πH' c (c v)) :
    condExpert πA' c = condExpert πH' c := by
  funext w v
  simp only [condExpert]
  by_cases h : c v = c w
  · rw [if_pos h, if_pos h]
    have hv := hagree v
    rw [h] at hv
    exact hv
  · rw [if_neg h, if_neg h, zero_div, zero_div]

theorem TT_of_cond_agree (πH' πA' : W → F) (c : W → ι)
    (hπH' : ∀ w, 0 < πH' w)
    (hagree : ∀ v, πA' v / fiberMass πA' c (c v)
                     = πH' v / fiberMass πH' c (c v)) :
    TT πH' (condExpert πA' c) := by
  rw [condExpert_eq_of_cond_agree πH' πA' c hagree]
  exact TT_condExpert πH' c hπH'

/-- Conditional probabilities sum to 1 over each (inhabited) fiber. -/
lemma cond_sum_one (π : W → F) (c : W → ι) (hπ : ∀ w, 0 < π w) (w0 : W) :
    (∑ v ∈ Finset.univ.filter (fun v => c v = c w0),
        π v / fiberMass π c (c v)) = 1 := by
  have hM : 0 < fiberMass π c (c w0) := fiberMass_pos π c hπ w0
  have h1 : (∑ v ∈ Finset.univ.filter (fun v => c v = c w0),
        π v / fiberMass π c (c v))
      = (∑ v ∈ Finset.univ.filter (fun v => c v = c w0), π v)
          / fiberMass π c (c w0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [(Finset.mem_filter.mp hv).2]
  have h2 : (∑ v ∈ Finset.univ.filter (fun v => c v = c w0), π v)
      = fiberMass π c (c w0) := by
    simp only [fiberMass]
    rw [Finset.sum_filter]
  rw [h1, h2, div_self (ne_of_gt hM)]

/-- **The exact characterization.**  For positive priors: `πH` Totally Trusts
the `πA`-conditional expert of a partition IFF the two priors' conditionals
agree on every cell.  (⇐ is lemma 1 via expert equality; ⇒ is the mismatch
witness, with the pivot step: if conditionals differ anywhere, then — both
summing to 1 over the fiber — some world has a strict `>` in the direction
the witness needs.) -/
theorem TT_condExpert_cross_iff (πH' πA' : W → F) (c : W → ι)
    (hπH' : ∀ w, 0 < πH' w) (hπA' : ∀ w, 0 < πA' w) :
    TT πH' (condExpert πA' c)
      ↔ ∀ v, πA' v / fiberMass πA' c (c v) = πH' v / fiberMass πH' c (c v) := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    obtain ⟨v0, hv0⟩ := hne
    by_cases hex : ∃ v1, πH' v1 / fiberMass πH' c (c v1)
        < πA' v1 / fiberMass πA' c (c v1)
    · obtain ⟨v1, hv1⟩ := hex
      exact TT_fails_of_cond_mismatch πH' πA' c hπH' hπA' v1 hv1 h
    · push_neg at hex
      -- everywhere πA-conditional ≤ πH-conditional, strict at v0; but both
      -- sum to 1 over v0's fiber — contradiction.
      have hlt : πA' v0 / fiberMass πA' c (c v0)
          < πH' v0 / fiberMass πH' c (c v0) := lt_of_le_of_ne (hex v0) hv0
      have hsum : (∑ v ∈ Finset.univ.filter (fun v => c v = c v0),
            πA' v / fiberMass πA' c (c v))
          < ∑ v ∈ Finset.univ.filter (fun v => c v = c v0),
            πH' v / fiberMass πH' c (c v) := by
        refine Finset.sum_lt_sum (fun i _ => hex i) ⟨v0, ?_, hlt⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v0, rfl⟩
      rw [cond_sum_one πA' c hπA' v0, cond_sum_one πH' c hπH' v0] at hsum
      exact lt_irrefl 1 hsum
  · exact TT_of_cond_agree πH' πA' c hπH'

/-- **Sharper recovery witness** (found by the EXEC sweep): prior identity is
sufficient but NOT necessary.  These priors DIFFER, yet the long edge holds,
because their conditionals agree on every `F_B` cell.  Run2's slogan "the
obstruction is prior mismatch" is imprecise; the exact lever is CONDITIONAL
mismatch on a cell of `F_B`. -/
def πH₂ : Fin 3 → ℚ := fun w => if w = 2 then 2/3 else 1/6
def πA₂ : Fin 3 → ℚ := fun _ => 1/3

theorem sharper_recovery_priors_differ : πH₂ ≠ πA₂ := by
  intro h
  have h0 := congrFun h 0
  norm_num [πH₂, πA₂] at h0

theorem sharper_recovery : TT πH₂ (condExpert πA₂ cB) := by
  refine TT_of_cond_agree πH₂ πA₂ cB (fun w => by fin_cases w <;> norm_num [πH₂, πA₂]) ?_
  intro v
  fin_cases v <;>
    norm_num [πH₂, πA₂, cB, fiberMass, Fin.sum_univ_three]

end TTTrans

/-! ## Axiom audit — every main theorem must use only the three standard
Mathlib axioms `[propext, Classical.choice, Quot.sound]` and NOT `sorryAx`. -/
#print axioms TTTrans.TT_condExpert
#print axioms TTTrans.link1
#print axioms TTTrans.link2
#print axioms TTTrans.long_edge_gap
#print axioms TTTrans.long_edge_fails
#print axioms TTTrans.TT_not_transitive
#print axioms TTTrans.recovery
#print axioms TTTrans.priors_differ
#print axioms TTTrans.PB_not_piH_conditional
#print axioms TTTrans.cA_nontrivial
#print axioms TTTrans.cB_nontrivial
#print axioms TTTrans.priors_sum_one
#print axioms TTTrans.experts_row_stochastic
#print axioms TTTrans.TT_fails_of_cond_mismatch
#print axioms TTTrans.TT_of_cond_agree
#print axioms TTTrans.TT_condExpert_cross_iff
#print axioms TTTrans.sharper_recovery
#print axioms TTTrans.sharper_recovery_priors_differ
