import Cleanroom.Decision.DpFairnessReloc.Fair
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness

/-!
# `dp-local-opt`: strict local maxima and the fairness grades (T11 / T16, repair round 1)

Audit r1 fidelity B1: `twoStag_HH_strict_local_max` exhibits a strict non-global local maximum of
`V` on an *almost-fair* tree, but dp-cf-2-026's extension question is about *strongly fair* trees
(`dp-fairness-reloc`'s `StronglyFair := FairWrt (fun _ => LabIso)`: every two nodes of a fiber
have labelled-isomorphic subtrees). This module

* proves `twoStag` is **not** strongly fair (`twoStag_not_stronglyFair`: its two `p2`-nodes have
  subtrees `[S → (S,S):2, H → (S,H):0]` and `[S → (H,S):0, H → (H,H):1]`), so T11(b) answers only
  the almost-fair form of the question;
* defines a strict local maximum of `V_B` at a procedure (`IsStrictLocalMax`: a sup-norm
  neighbourhood on the node distributions, strictness at the queried points);
* proves the **gated shape lemma** `gated_strictLocalMax_global`: for
  `V(p, q) = H(p) + G(p) f(q)` with `H, G, f` affine and `G ≥ 0` on `[0,1]`, every strict local
  maximum on `[0,1]²` is global (the shape strong fairness forces on a two-point tree: one point's
  nodes gate the other's, all gated subtrees isomorphic);
* instantiates it on the whole `twoPoint` family (one node per point, hence strongly fair:
  `twoPoint_stronglyFair`): `twoPoint_strictLocalMax_isOptimal` — on `fairDepth2` in particular,
  the weak non-global local maximum of T11(a) cannot be sharpened to a strict one;
* stated (repair round 1) the strongly-fair form of the extension question as an open theorem,
  `stronglyFair_strictLocalMax_isOptimal`, with the informal argument in the findings (F10) — now
  **proved** in `GatedInduction.lean` (repair round 2);
* (repair round 2, audit r2 fidelity B1 / adversarial N1–N2) **inhabits `IsStrictLocalMax`**:
  on the strongly fair `twoPoint 2 4 1` at its optimum `(in, x)` (`twoPoint_inX_isStrictLocalMax`,
  so the `twoPoint` theorem and the general theorem are not vacuous:
  `stronglyFair_strictLocalMax_inhabited`), and on the almost-fair `twoStag` at `(H,H)`
  (`twoStag_HH_isStrictLocalMax`), which states the almost-fair refutation in the predicate
  itself (`almostFair_strictLocalMax_not_isOptimal`); and marks the predicate's boundary: a leaf
  (`leaf_isStrictLocalMax`), an unreached queried point (`outY_not_isStrictLocalMax`), and a tree
  with no strict local maximum at all (`twoPoint541_no_strictLocalMax`).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-! ### `twoStag` is not strongly fair -/

section notStronglyFair

/-- The `p2`-node under `S` (`.a`) at the root of `twoStag`.
Source: none: infrastructure
Kind: D -/
def p2underS : twoStag.DecNode := some ⟨.a, none⟩

/-- The `p2`-node under `H` (`.b`) at the root of `twoStag`.
Source: none: infrastructure
Kind: D -/
def p2underH : twoStag.DecNode := some ⟨.b, none⟩

/-- `p2underS` is in the `p2`-fiber.
Source: none: infrastructure
Kind: L -/
theorem p2underS_mem : p2underS ∈ fiber twoStag .p2 :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- `p2underH` is in the `p2`-fiber.
Source: none: infrastructure
Kind: L -/
theorem p2underH_mem : p2underH ∈ fiber twoStag .p2 :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- The two `p2`-subtrees of `twoStag` are not labelled-isomorphic: their `S`-leaves are
`((S,S), 2)` and `((H,S), 0)`.
Source: [[fable-slop-notes]] §1 (structurally distinguishable same-point nodes); audit r1
fidelity B1's probe `NotStronglyFair.lean`, adopted
Kind: P -/
theorem twoStag_p2_subtrees_not_iso :
    ¬ LabIso (subtreeAt twoStag p2underS) (subtreeAt twoStag p2underH) := by
  intro h
  simp only [p2underS, p2underH, twoStag, subtreeAt_decision_some, subtreeAt_decision_none] at h
  cases h with
  | decision _ _ _ hchild =>
    have hS := hchild .a
    cases hS

/-- **`twoStag` is almost fair and not strongly fair.** Its two `p2`-nodes have non-isomorphic
subtrees, so `dp-fairness-reloc`'s `StronglyFair` fails while `AlmostFair` holds
(`twoStag_HH_strict_local_max.1`). Hence T11(b)'s strict non-global local maximum lives on the
almost-fair class and does not answer dp-cf-2-026's strongly-fair extension question.
Source: dp-cf-2-026 (extension flag: "does a *strongly fair* tree's `V` have strict non-global
local maxima?"); `fair-repair.md` §0 (grade 1, `Fair_≅`); audit r1 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoStag_not_stronglyFair : AlmostFair twoStag ∧ ¬ StronglyFair twoStag :=
  ⟨twoStag_HH_strict_local_max.1, fun h =>
    twoStag_p2_subtrees_not_iso (h .p2 p2underS p2underS_mem p2underH p2underH_mem)⟩

end notStronglyFair

/-! ### One node per point is strongly fair -/

section injective

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- A tree whose node-to-point map is injective (one node per point) is strongly fair: every
fiber is a singleton and `LabIso` is reflexive.
Source: `fair-repair.md` §0 (trivial fibers); none: infrastructure
Kind: L -/
theorem StronglyFair.of_injective_pt {B : Tree Ω ι acts K} (h : Function.Injective (pt B)) :
    StronglyFair B := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  have : q = q' := h (hq.trans hq'.symm)
  subst this
  exact LabIso.refl _

end injective

section twoPointFair

/-- `twoPoint` has one node per point: its node-to-point map is injective.
Source: none: infrastructure
Kind: L -/
theorem twoPoint_pt_injective (rOut rX rY : ℚ) :
    Function.Injective (pt (twoPoint rOut rX rY)) := by
  intro q q' h
  rcases q with _ | ⟨a, q⟩
  · rcases q' with _ | ⟨a', q'⟩
    · rfl
    · cases a'
      · exact q'.elim
      · rcases q' with _ | ⟨a'', q''⟩
        · exact absurd h (by simp [twoPoint, pt])
        · cases a'' <;> exact q''.elim
  · cases a
    · exact q.elim
    · rcases q with _ | ⟨a'', q''⟩
      · rcases q' with _ | ⟨a', q'⟩
        · exact absurd h (by simp [twoPoint, pt])
        · cases a'
          · exact q'.elim
          · rcases q' with _ | ⟨a''', q'''⟩
            · rfl
            · cases a''' <;> exact q'''.elim
      · cases a'' <;> exact q''.elim

/-- **Every `twoPoint` tree is strongly fair** (one node per point), in particular `fairDepth2`.
Source: `fair-repair.md` §0; dp-cf-2-026(b) ("a depth-2 strongly fair tree")
Kind: L -/
theorem twoPoint_stronglyFair (rOut rX rY : ℚ) : StronglyFair (twoPoint rOut rX rY) :=
  StronglyFair.of_injective_pt (twoPoint_pt_injective rOut rX rY)

end twoPointFair

/-! ### Affine functions on `[0,1]`: a strict local maximum is global -/

section affine

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Some point of `[0,1]` other than `q₀` lies within `ε` of it.
Source: none: infrastructure
Kind: L -/
theorem exists_ne_near (q₀ ε : K) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) (hε : 0 < ε) :
    ∃ q, 0 ≤ q ∧ q ≤ 1 ∧ q ≠ q₀ ∧ |q - q₀| ≤ ε := by
  by_cases hh : q₀ < 1
  · have hlt : q₀ < min 1 (q₀ + ε) := lt_min hh (by linarith)
    refine ⟨min 1 (q₀ + ε), le_min zero_le_one (by linarith), min_le_left _ _, hlt.ne', ?_⟩
    rw [abs_of_pos (by linarith)]
    have := min_le_right 1 (q₀ + ε)
    linarith
  · have hq : q₀ = 1 := le_antisymm h1 (not_lt.mp hh)
    subst hq
    have hlt : max 0 (1 - ε) < 1 := max_lt one_pos (by linarith)
    refine ⟨max 0 (1 - ε), le_max_left _ _, max_le zero_le_one (by linarith), hlt.ne, ?_⟩
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    have := le_max_right 0 (1 - ε)
    linarith

/-- **An affine function on `[0,1]` with a strict local maximum at `q₀` is globally maximised
at `q₀`** (the strict local maximum forces `q₀` to be the endpoint the function increases
towards, or the function to be constant, which strictness rules out).
Source: none: infrastructure (the one-variable step of the gated shape lemma)
Kind: P -/
theorem affine_le_of_strictLocalMax (f₀ f₁ q₀ : K) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) (ε : K)
    (hε : 0 < ε)
    (hloc : ∀ q, 0 ≤ q → q ≤ 1 → q ≠ q₀ → |q - q₀| ≤ ε → f₀ + f₁ * q < f₀ + f₁ * q₀) :
    ∀ q, 0 ≤ q → q ≤ 1 → f₀ + f₁ * q ≤ f₀ + f₁ * q₀ := by
  intro q hq0 hq1
  rcases lt_trichotomy f₁ 0 with hneg | hzero | hpos
  · by_cases hq₀ : q₀ = 0
    · subst hq₀; nlinarith
    · exfalso
      have hq₀pos : 0 < q₀ := lt_of_le_of_ne h0 (Ne.symm hq₀)
      have hq'lt : max 0 (q₀ - ε) < q₀ := max_lt hq₀pos (by linarith)
      have hdist : |max 0 (q₀ - ε) - q₀| ≤ ε := by
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        have := le_max_right 0 (q₀ - ε)
        linarith
      have h1' := hloc (max 0 (q₀ - ε)) (le_max_left _ _) (by linarith) hq'lt.ne hdist
      have h2' := mul_lt_mul_of_neg_left hq'lt hneg
      linarith
  · subst hzero; simp
  · by_cases hq₀ : q₀ = 1
    · subst hq₀; nlinarith
    · exfalso
      have hq₀lt : q₀ < 1 := lt_of_le_of_ne h1 hq₀
      have hq'gt : q₀ < min 1 (q₀ + ε) := lt_min hq₀lt (by linarith)
      have hdist : |min 1 (q₀ + ε) - q₀| ≤ ε := by
        rw [abs_of_pos (by linarith)]
        have := min_le_right 1 (q₀ + ε)
        linarith
      have h1' := hloc (min 1 (q₀ + ε)) (by linarith) (min_le_left _ _) hq'gt.ne' hdist
      have h2' := mul_lt_mul_of_pos_left hq'gt hpos
      linarith

/-- **The gated shape lemma: for `V(p, q) = H(p) + G(p) f(q)` with `H`, `G`, `f` affine and
`G ≥ 0` on `[0,1]`, a strict local maximum of `V` on `[0,1]²` is a global maximum.** Proof:
`G(p₀) > 0` (else `V(p₀, ·)` is constant, contradicting strictness); so `f` has a strict local
maximum at `q₀`, hence `f ≤ f(q₀)` on `[0,1]`; so `V(p, q) ≤ V(p, q₀)` for every `p`; and
`V(·, q₀)` is affine with a strict local maximum at `p₀`, hence `≤ V(p₀, q₀)`. This is the shape
F10's informal argument assigns to `V` on a strongly fair two-point tree (one point's nodes gate
the other's, all gated subtrees isomorphic, `G` the gated reach mass); it is instantiated in Lean
on the `twoPoint` family (`twoPoint_strictLocalMax_isOptimal`). The general derivation from
`StronglyFair` is `GatedInduction.lean` (`value_deviate_eq_gated`, one point at a time), which
proves the general theorem `stronglyFair_strictLocalMax_isOptimal` without going through this
two-variable lemma.
Source: audit r1 fidelity B1 (the auditor's sketch, made a theorem); dp-cf-2-026 (extension
question)
Kind: P
Fidelity: exact (the abstract two-point shape)
Hyps: (a) all -/
theorem gated_strictLocalMax_global (h₀ h₁ g₀ g₁ f₀ f₁ : K)
    (hG : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ g₀ + g₁ * p)
    (p₀ q₀ : K) (hp0 : 0 ≤ p₀) (hp1 : p₀ ≤ 1) (hq0 : 0 ≤ q₀) (hq1 : q₀ ≤ 1)
    (ε : K) (hε : 0 < ε)
    (hloc : ∀ p q, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → (p ≠ p₀ ∨ q ≠ q₀) →
      |p - p₀| ≤ ε → |q - q₀| ≤ ε →
      (h₀ + h₁ * p) + (g₀ + g₁ * p) * (f₀ + f₁ * q) <
        (h₀ + h₁ * p₀) + (g₀ + g₁ * p₀) * (f₀ + f₁ * q₀)) :
    ∀ p q, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      (h₀ + h₁ * p) + (g₀ + g₁ * p) * (f₀ + f₁ * q) ≤
        (h₀ + h₁ * p₀) + (g₀ + g₁ * p₀) * (f₀ + f₁ * q₀) := by
  have hself : |p₀ - p₀| ≤ ε := by simp [hε.le]
  have hselfq : |q₀ - q₀| ≤ ε := by simp [hε.le]
  -- Step 1: `G(p₀) > 0`.
  have hGpos : 0 < g₀ + g₁ * p₀ := by
    rcases (hG p₀ hp0 hp1).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq0', hq1', hne, hd⟩ := exists_ne_near q₀ ε hq0 hq1 hε
      have := hloc p₀ q hp0 hp1 hq0' hq1' (Or.inr hne) hself hd
      rw [← h] at this
      simp at this
  -- Step 2: `f ≤ f(q₀)` on `[0,1]`.
  have hf : ∀ q, 0 ≤ q → q ≤ 1 → f₀ + f₁ * q ≤ f₀ + f₁ * q₀ := by
    apply affine_le_of_strictLocalMax f₀ f₁ q₀ hq0 hq1 ε hε
    intro q hq0' hq1' hne hd
    have := hloc p₀ q hp0 hp1 hq0' hq1' (Or.inr hne) hself hd
    have h2 : (g₀ + g₁ * p₀) * (f₀ + f₁ * q) < (g₀ + g₁ * p₀) * (f₀ + f₁ * q₀) := by linarith
    exact lt_of_mul_lt_mul_left h2 hGpos.le
  -- Step 3: `V(·, q₀)` is affine with a strict local maximum at `p₀`.
  have hp : ∀ p, 0 ≤ p → p ≤ 1 →
      (h₀ + g₀ * (f₀ + f₁ * q₀)) + (h₁ + g₁ * (f₀ + f₁ * q₀)) * p ≤
        (h₀ + g₀ * (f₀ + f₁ * q₀)) + (h₁ + g₁ * (f₀ + f₁ * q₀)) * p₀ := by
    apply affine_le_of_strictLocalMax _ _ p₀ hp0 hp1 ε hε
    intro p hp0' hp1' hne hd
    have := hloc p q₀ hp0' hp1' hq0 hq1 (Or.inl hne) hd hselfq
    linarith
  -- Step 4: combine.
  intro p q hp0' hp1' hq0' hq1'
  calc (h₀ + h₁ * p) + (g₀ + g₁ * p) * (f₀ + f₁ * q)
      ≤ (h₀ + h₁ * p) + (g₀ + g₁ * p) * (f₀ + f₁ * q₀) := by
        have := mul_le_mul_of_nonneg_left (hf q hq0' hq1') (hG p hp0' hp1')
        linarith
    _ ≤ (h₀ + h₁ * p₀) + (g₀ + g₁ * p₀) * (f₀ + f₁ * q₀) := by
        have := hp p hp0' hp1'
        linarith

end affine

/-! ### Strict local maxima of `V_B` at a procedure -/

section strictLocalMax

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- **A strict local maximum of `V_B` at `C`**: some `ε > 0` such that every procedure within
`ε` of `C` in every node weight (sup norm on `∏_d Δ(A_d)`) that differs from `C` at a queried
point has strictly smaller value. Strictness is required only at queried points because `V_B`
does not read the others (`value_congr_queried`). Scope (audit r2 adversarial N2): strictness is
demanded at *every* queried point, so the notion bites only at procedures that reach every
queried point — a procedure leaving a queried point unreached is never a strict local maximum,
even at a global optimum (`outY_not_isStrictLocalMax`), some trees have no strict local maximum
at all (`twoPoint541_no_strictLocalMax`), and on a leaf every procedure is one
(`leaf_isStrictLocalMax`). This is the reading under which dp-cf-2-026 calls `fairDepth2`'s
face `p_in = 0` a *weak* maximum. Inhabited: `twoPoint_inX_isStrictLocalMax`,
`twoStag_HH_isStrictLocalMax`.
Source: dp-cf-2-026 ("strict non-global local maxima"); `repair/dynamic.md` Open 8; mandate T11
Kind: D
Fidelity: exact (sup-norm neighbourhoods; that any norm on a finite product gives the same
notion is a remark, not formalised) -/
def IsStrictLocalMax (C : Proc ι acts K) (B : Tree Ω ι acts K) : Prop :=
  ∃ ε > 0, ∀ C' : Proc ι acts K, (∃ d ∈ queried B, C' d ≠ C d) →
    (∀ d a, |(C' d).w a - (C d).w a| ≤ ε) → value C' B < value C B

/-! The strongly-fair form of dp-cf-2-026's extension question,
`stronglyFair_strictLocalMax_isOptimal : StronglyFair B → IsStrictLocalMax C B → IsOptimal C B`,
was stated here with `sorry` in repair round 1 and is **proved** in `GatedInduction.lean`
(repair round 2), by F10's induction on the gating order. -/

end strictLocalMax

section twoPointStrict

/-- `.p1` and `.p2` are queried on every `twoPoint` tree.
Source: none: infrastructure
Kind: L -/
theorem twoPoint_queried (rOut rX rY : ℚ) :
    Pt2.p1 ∈ queried (twoPoint rOut rX rY) ∧ Pt2.p2 ∈ queried (twoPoint rOut rX rY) := by
  refine ⟨mem_queried_decision _ _, ?_⟩
  simp only [twoPoint, queried_decision, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact Or.inr ⟨.b, mem_queried_decision _ _⟩

/-- **On every `twoPoint` tree (strongly fair, one node per point) a strict local maximum of `V`
is a global maximum**: `V(p, q) = p r_out + (1 − p)(q r_x + (1 − q) r_y)` is the gated shape
`H(p) + G(p) f(q)` with `G(p) = 1 − p ≥ 0`. In particular T11(a)'s weak non-global local
maximum on `fairDepth2` cannot be sharpened to a strict one: on this strongly fair family
dp-cf-2-026's extension question has a negative answer. Content: the hypothesis is inhabited
(`twoPoint_inX_isStrictLocalMax`: the optimum `(in, x)` of `twoPoint 2 4 1`), and it lives on
trees whose optimum reaches both points — on `twoPoint 5 4 1` no procedure is a strict local
maximum (`twoPoint541_no_strictLocalMax`), so there the theorem is vacuous.
Source: dp-cf-2-026(b) ("a depth-2 strongly fair tree … the ledger's evidence says no, on one
tree"); `repair/dynamic.md` Open 8; audit r1 fidelity B1
Kind: P
Fidelity: exact (the `twoPoint` family; the general strongly-fair statement is
`stronglyFair_strictLocalMax_isOptimal`, `GatedInduction.lean`, of which this is now a special
case)
Hyps: (a) all -/
theorem twoPoint_strictLocalMax_isOptimal (rOut rX rY : ℚ) (C : Proc Pt2 (fun _ => Act2) ℚ)
    (h : IsStrictLocalMax C (twoPoint rOut rX rY)) : IsOptimal C (twoPoint rOut rX rY) := by
  obtain ⟨p, q, hp0, hp1, hq0, hq1, rfl⟩ :
      ∃ p q hp0 hp1 hq0 hq1, C = proc2 p q hp0 hp1 hq0 hq1 :=
    ⟨_, _, _, _, _, _, Proc.pt2_eq_proc2 C⟩
  obtain ⟨ε, hε, hloc⟩ := h
  rw [isOptimal_proc2_iff]
  intro r s r0 r1 s0 s1
  rw [twoPoint_value, twoPoint_value]
  have key := gated_strictLocalMax_global (K := ℚ) 0 rOut 1 (-1) rY (rX - rY)
    (fun p' hp0' hp1' => by linarith) p q hp0 hp1 hq0 hq1 ε hε ?_ r s r0 r1 s0 s1
  · linarith
  · intro p' q' hp0' hp1' hq0' hq1' hne hdp hdq
    have hval := hloc (proc2 p' q' hp0' hp1' hq0' hq1') ?_ ?_
    · rw [twoPoint_value, twoPoint_value] at hval
      linarith
    · rcases hne with hne | hne
      · refine ⟨.p1, (twoPoint_queried rOut rX rY).1, fun heq => hne ?_⟩
        have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) heq
        simpa using this
      · refine ⟨.p2, (twoPoint_queried rOut rX rY).2, fun heq => hne ?_⟩
        have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) heq
        simpa using this
    · intro d x
      cases d <;> cases x
      · simpa using hdp
      · simp only [proc2_p1, FinDistr.act2_b]
        rw [show (1 - p') - (1 - p) = -(p' - p) by ring, abs_neg]; exact hdp
      · simpa using hdq
      · simp only [proc2_p2, FinDistr.act2_b]
        rw [show (1 - q') - (1 - q) = -(q' - q) by ring, abs_neg]; exact hdq

end twoPointStrict

/-! ### `IsStrictLocalMax` is inhabited (repair round 2)

Audit r2 fidelity B1 / adversarial N1: nothing in the package inhabited `IsStrictLocalMax`, so
`twoPoint_strictLocalMax_isOptimal` and the open statement had no witness of their hypothesis
package. Both auditors' probes proved the inhabitants below (adversarial `StrictLocalMax.lean`,
fidelity `Inhabited.lean`, namespace `…AuditR2`); adopted here with the adversarial probe's
statements and `ε = 1/3`. -/

section inhabited

/-- **`(H,H)` on `twoStag` is a strict local maximum in the package's own predicate**
(`ε = 1/3`, from the explicit inequality `twoStag_HH_strict_local_max`).
Source: mandate T11(b); audit r2 adversarial N1 (probe `twoStag_HH_isStrictLocalMax`, adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoStag_HH_isStrictLocalMax : IsStrictLocalMax profHH twoStag := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro C' hne hnear
  obtain ⟨p, q, hp0, hp1, hq0, hq1, rfl⟩ :
      ∃ p q hp0 hp1 hq0 hq1, C' = proc2 p q hp0 hp1 hq0 hq1 :=
    ⟨_, _, _, _, _, _, Proc.pt2_eq_proc2 C'⟩
  have hp := hnear .p1 .a
  have hq := hnear .p2 .a
  simp only [proc2_p1, proc2_p2, FinDistr.act2_a, profHH, sub_zero] at hp hq
  rw [abs_le] at hp hq
  have hne' : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d, _, hd⟩ := hne
    exact hd rfl
  have key := twoStag_HH_strict_local_max.2.1 p q hp0 hp.2 hq0 hq.2 hne'
  rw [twoStag_HH_strict_local_max.2.2.1]
  exact key

/-- **The almost-fair form of the general theorem, refuted in the predicate**: an almost-fair tree
(`twoStag`) with a strict local maximum in the sense of `IsStrictLocalMax` (`(H,H)`) that is not
optimal. Strong fairness is therefore necessary for `stronglyFair_strictLocalMax_isOptimal`
(`GatedInduction.lean`): its conclusion fails one fairness grade down.
Source: dp-cf-2-026 (extension flag); mandate T11(b); audit r2 adversarial N1 (probe, adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem almostFair_strictLocalMax_not_isOptimal :
    AlmostFair twoStag ∧ IsStrictLocalMax profHH twoStag ∧ ¬ IsOptimal profHH twoStag :=
  ⟨twoStag_HH_strict_local_max.1, twoStag_HH_isStrictLocalMax,
    twoStag_HH_coherent_thm1_not_optimal.2.2.2.1⟩

/-- The procedure `(in, x)` on a two-point tree: `proc2 0 1` (`C(p1)(out) = 0`, `C(p2)(x) = 1`).
Source: none: infrastructure
Kind: D -/
abbrev inX : Proc Pt2 (fun _ => Act2) ℚ := proc2 0 1 le_rfl zero_le_one zero_le_one le_rfl

/-- **`IsStrictLocalMax` is inhabited on a strongly fair tree**: on `twoPoint 2 4 1` the global
optimum `(in, x)` (`V = 4`) is a strict local maximum with `ε = 1/3` — for `q ≥ 2/3`,
`V(p, q) − 4 = p(1 − 3q) − 3(1 − q) < 0` unless `p = 0` and `q = 1`. Hence
`twoPoint_strictLocalMax_isOptimal`'s hypothesis is satisfiable.
Source: dp-cf-2-026(b); audit r2 fidelity B1 (probe `twoPoint_inX_strictLocalMax`, `ε = 1/2`)
and adversarial N1 (probe `twoPoint_inX_isStrictLocalMax`, `ε = 1/3`; adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoPoint_inX_isStrictLocalMax : IsStrictLocalMax inX (twoPoint 2 4 1) := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro C' hne hnear
  obtain ⟨p, q, hp0, hp1, hq0, hq1, rfl⟩ :
      ∃ p q hp0 hp1 hq0 hq1, C' = proc2 p q hp0 hp1 hq0 hq1 :=
    ⟨_, _, _, _, _, _, Proc.pt2_eq_proc2 C'⟩
  have hp := hnear .p1 .a
  have hq := hnear .p2 .a
  simp only [proc2_p1, proc2_p2, FinDistr.act2_a, inX, sub_zero] at hp hq
  rw [abs_le] at hp hq
  have hne' : p ≠ 0 ∨ q ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d, _, hd⟩ := hne
    exact hd rfl
  rw [twoPoint_value, twoPoint_value]
  have h3q : 0 ≤ 3 * q - 1 := by linarith
  rcases hne' with hp' | hq'
  · have hpos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp')
    nlinarith [mul_pos hpos (show (0:ℚ) < 3 * q - 1 by linarith), mul_nonneg hp0 h3q]
  · have hlt : q < 1 := lt_of_le_of_ne hq1 hq'
    nlinarith [mul_nonneg hp0 h3q]

/-- **The general theorem's hypothesis package is inhabited on a tree where `V` is not constant**:
`twoPoint 2 4 1` is strongly fair, `(in, x)` is a strict local maximum there, and `V` takes the
values `4` (at `(in, x)`) and `2` (at `(out, y)`).
Source: dp-cf-2-026 (extension flag); audit r2 adversarial N1 (probe, adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem stronglyFair_strictLocalMax_inhabited :
    StronglyFair (twoPoint 2 4 1) ∧ IsStrictLocalMax inX (twoPoint 2 4 1) ∧
    value inX (twoPoint 2 4 1) = 4 ∧ value outY (twoPoint 2 4 1) = 2 :=
  ⟨twoPoint_stronglyFair 2 4 1, twoPoint_inX_isStrictLocalMax, by rw [twoPoint_value]; norm_num,
    by rw [twoPoint_value]; norm_num⟩

end inhabited

/-! ### Boundaries of `IsStrictLocalMax` (repair round 2, audit r2 adversarial N2) -/

section boundary

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

omit [∀ d, DecidableEq (acts d)] in
/-- On a leaf (no queried point) every procedure is a strict local maximum and optimal: the
general theorem is trivially true there.
Source: none: infrastructure (audit r2 adversarial N2, probe adopted)
Kind: N-
Fidelity: n/a -/
theorem leaf_isStrictLocalMax (C : Proc ι acts K) (ω : Ω) (r : K) :
    IsStrictLocalMax C (leaf ω r : Tree Ω ι acts K) ∧ IsOptimal C (leaf ω r) := by
  refine ⟨⟨1, one_pos, fun C' hne _ => ?_⟩, fun C' => by simp⟩
  obtain ⟨d, hd, _⟩ := hne
  simp [queried] at hd

end boundary

section boundaryTwoPoint

/-- **`(out, y)` on `(2;4,1)` is not a strict local maximum**: `p2` is queried but unreached, so
changing `C(p2)` leaves `V = 2` unchanged — strictness at every queried point is demanded. (The
same profile is T7's coherent, Theorem-1-ratified, non-optimal witness
`outY_coherent_thm1_not_optimal`.)
Source: dp-cf-2-026 (the "weak" maximum on the face `p_in = 0`); audit r2 adversarial N2 (probe,
adopted)
Kind: N-
Fidelity: exact -/
theorem outY_not_isStrictLocalMax : ¬ IsStrictLocalMax outY (twoPoint 2 4 1) := by
  rintro ⟨ε, hε, h⟩
  have hε0 : 0 ≤ min 1 ε := le_min zero_le_one hε.le
  have hε1 : min 1 ε ≤ 1 := min_le_left _ _
  have hne : ∃ d ∈ queried (twoPoint 2 4 1),
      proc2 1 (min 1 ε) zero_le_one le_rfl hε0 hε1 d ≠ outY d := by
    refine ⟨.p2, (twoPoint_queried 2 4 1).2, fun heq => ?_⟩
    have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) heq
    simp only [proc2_p2, FinDistr.act2_a, outY] at this
    have hεpos : 0 < min 1 ε := lt_min one_pos hε
    linarith
  have hnear : ∀ d x, |(proc2 1 (min 1 ε) zero_le_one le_rfl hε0 hε1 d).w x - (outY d).w x| ≤ ε := by
    intro d x
    cases d <;> cases x
    · simp [outY, hε.le]
    · simp [outY, hε.le]
    · simp only [proc2_p2, FinDistr.act2_a, outY, sub_zero]
      rw [abs_of_nonneg hε0]; exact min_le_right _ _
    · simp only [proc2_p2, FinDistr.act2_b, outY]
      rw [show (1 - min 1 ε) - (1 - 0) = -(min 1 ε) by ring, abs_neg, abs_of_nonneg hε0]
      exact min_le_right _ _
  have := h _ hne hnear
  rw [twoPoint_value, twoPoint_value] at this
  norm_num at this

/-- **`twoPoint 5 4 1` has no strict local maximum at all**: below `p = 1` raising `p` strictly
improves `V` (`∂V/∂p = 4 − 3q ≥ 1`), and at `p = 1` the point `p2` is unreached. On this tree
`twoPoint_strictLocalMax_isOptimal` is vacuous — the theorem's content lives on trees whose
optimum reaches every point.
Source: none: infrastructure (audit r2 adversarial N2, probe adopted)
Kind: N-
Fidelity: exact -/
theorem twoPoint541_no_strictLocalMax (C : Proc Pt2 (fun _ => Act2) ℚ) :
    ¬ IsStrictLocalMax C (twoPoint 5 4 1) := by
  obtain ⟨p, q, hp0, hp1, hq0, hq1, rfl⟩ :
      ∃ p q hp0 hp1 hq0 hq1, C = proc2 p q hp0 hp1 hq0 hq1 :=
    ⟨_, _, _, _, _, _, Proc.pt2_eq_proc2 C⟩
  rintro ⟨ε, hε, h⟩
  rcases lt_or_eq_of_le hp1 with hlt | rfl
  · obtain ⟨p', hp'0, hp'1, hpp', hp'le⟩ : ∃ p', 0 ≤ p' ∧ p' ≤ 1 ∧ p < p' ∧ p' ≤ p + ε :=
      ⟨min 1 (p + ε), le_min zero_le_one (by linarith), min_le_left _ _,
        lt_min hlt (by linarith), min_le_right _ _⟩
    have hne : ∃ d ∈ queried (twoPoint 5 4 1),
        proc2 p' q hp'0 hp'1 hq0 hq1 d ≠ proc2 p q hp0 hp1 hq0 hq1 d := by
      refine ⟨.p1, (twoPoint_queried 5 4 1).1, fun heq => ?_⟩
      have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) heq
      simp only [proc2_p1, FinDistr.act2_a] at this
      linarith
    have hnear : ∀ d x,
        |(proc2 p' q hp'0 hp'1 hq0 hq1 d).w x - (proc2 p q hp0 hp1 hq0 hq1 d).w x| ≤ ε := by
      intro d x
      cases d <;> cases x
      · simp only [proc2_p1, FinDistr.act2_a]
        rw [abs_of_nonneg (by linarith)]; linarith
      · simp only [proc2_p1, FinDistr.act2_b]
        rw [show (1 - p') - (1 - p) = -(p' - p) by ring, abs_neg, abs_of_nonneg (by linarith)]
        linarith
      · simp [hε.le]
      · simp [hε.le]
    have := h _ hne hnear
    rw [twoPoint_value, twoPoint_value] at this
    nlinarith [mul_pos (sub_pos.mpr hpp') (show (0:ℚ) < 4 - 3 * q by linarith)]
  · obtain ⟨q', hq'0, hq'1, hne', hd⟩ := exists_ne_near q ε hq0 hq1 hε
    have hne : ∃ d ∈ queried (twoPoint 5 4 1),
        proc2 1 q' zero_le_one le_rfl hq'0 hq'1 d ≠ proc2 1 q hp0 hp1 hq0 hq1 d := by
      refine ⟨.p2, (twoPoint_queried 5 4 1).2, fun heq => ?_⟩
      have := congrArg (fun m : FinDistr ℚ Act2 => m.w .a) heq
      simp only [proc2_p2, FinDistr.act2_a] at this
      exact hne' this
    have hnear : ∀ d x,
        |(proc2 1 q' zero_le_one le_rfl hq'0 hq'1 d).w x - (proc2 1 q hp0 hp1 hq0 hq1 d).w x| ≤ ε := by
      intro d x
      cases d <;> cases x
      · simp [hε.le]
      · simp [hε.le]
      · simpa using hd
      · simp only [proc2_p2, FinDistr.act2_b]
        rw [show (1 - q') - (1 - q) = -(q' - q) by ring, abs_neg]; exact hd
    have := h _ hne hnear
    rw [twoPoint_value, twoPoint_value] at this
    norm_num at this

end boundaryTwoPoint

end Cleanroom.Decision.DpLocalOpt
