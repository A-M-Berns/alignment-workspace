import Cleanroom.Decision.DpDutchBook.Defs
import Cleanroom.Decision.DpCalibration.Limit
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Found.DpCoreTree.NodeSums
import Mathlib.Algebra.Polynomial.Roots

/-!
# T7(a)–(b): the act-recording lemma at F3′ points and the tremble-pinned value as a ratio

Over a generic ordered field `K` (the continuity statements over `ℝ` are in `MsrExists.lean`).

* `ActRecordingStruct obs actEv B d` — **F3′ as a structural fact of the tree** (for every
  procedure): every node-action-veridical `d`-node is subtree-veridical, and every
  chance-positive `O_d`-leaf passes exactly one node-action-veridical `d`-node. Equivalent to
  `dp-core-tree`'s `ActRecording obs actEv C B d` for every `C` (`actRecording_of_struct`,
  `struct_of_actRecording_fullSupport`).
* `nu_actEv_inter_obs_of_struct` — **the recording lemma at F3′ points**: for *every* procedure
  `C`, `ν_C(a ∧ O_d) = C(d)(a) · ν_C(O_d)` (the real node's draw contributes the factor
  `C(d)(a)` once; upstream simulations sit inside `ν_C(O_d)`). `dp-referents-cdt`'s C2-1 is the
  same lemma; whichever lands first, the other cites.
* `paySum_eq_w_mul_qSum` — the payoff side: `𝔼_C[r · 1_{a ∧ O_d}] = C(d)(a) · Q_a(C)`, with
  `Q_a(C) = qSum` the leaf sum of `chanceWeight · (draw weights with one `⟨d, a⟩` factor erased)
  · payoff` — a polynomial in the weights of `C(d)`.
* `nuPoly_eq_trembleW_mul_nuPoly_obs`, `payPoly_eq_trembleW_mul_qPoly` — the same two
  factorisations at the level of `dp-calibration`'s `ε`-polynomials.
* `r3Val_eq_qSum_div` — **the tremble-pinned act value is `Q_a(m) / R(m)`** for every label
  `m`, including `m(a) = 0`, under the standing hypothesis `R(m) := ν_{C[d↦m]}(O_d) > 0`. This is
  C2-7's "ratio of polynomials with positive denominator", proved from the tree.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-! ## F3′ as a structural fact -/

/-- The node-action-veridical `d`-nodes of `B` (the "real" `d`-nodes of F3′; a `C`-free set).
Source: `cf-workflow/phase2-notes/repair/faithful.md` F3′ (via dp-cf-2-001)
Kind: D -/
noncomputable def navFiber (B : Tree Ω ι acts K) (d : ι) : Finset B.DecNode := by
  classical exact Finset.univ.filter fun q => pt B q = d ∧ NodeActionVeridical actEv B q

/-- Membership in `navFiber`. Source: none: infrastructure. Kind: L -/
theorem mem_navFiber (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ navFiber actEv B d ↔ pt B q = d ∧ NodeActionVeridical actEv B q := by
  unfold navFiber
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **F3′ as a structural property of the tree** (for every procedure): every node-action-veridical
`d`-node is subtree-veridical, and every chance-positive `O_d`-leaf passes exactly one
node-action-veridical `d`-node (upstream simulations of `d` are allowed, provided they are not
node-action-veridical).
Source: `faithful.md` F3′ as restated in dp-cf-2-001; mandate T7(a) ("`ActRecording obs actEv C'
B d` for every `C'` (structural)")
Kind: D
Fidelity: exact (`ActRecording` with "positive mass under `C`" replaced by "chance-positive",
which is the same set of leaves under every full-support procedure) -/
def ActRecordingStruct (B : Tree Ω ι acts K) (d : ι) : Prop :=
  (∀ q, pt B q = d → NodeActionVeridical actEv B q → SubtreeVeridical obs B q) ∧
  ∀ ℓ, 0 < chanceWeight B ℓ → world B ℓ ∈ obs d →
    ∃! q, q ∈ dNodesOn B d ℓ ∧ NodeActionVeridical actEv B q

/-- The structural form gives `ActRecording` for every procedure.
Source: none: infrastructure. Kind: L -/
theorem actRecording_of_struct {B : Tree Ω ι acts K} {d : ι}
    (h : ActRecordingStruct obs actEv B d) (C : Proc ι acts K) :
    ActRecording obs actEv C B d :=
  ⟨h.1, fun ℓ hpos hobs => h.2 ℓ (Positive.of_leafLaw_pos C hpos) hobs⟩

/-- `ActRecording` for one full-support procedure gives the structural form.
Source: none: infrastructure. Kind: L -/
theorem struct_of_actRecording_fullSupport {B : Tree Ω ι acts K} {d : ι} {C : Proc ι acts K}
    (hC : C.FullSupport) (h : ActRecording obs actEv C B d) :
    ActRecordingStruct obs actEv B d :=
  ⟨h.1, fun ℓ hpos hobs => h.2 ℓ (leafLaw_pos_of_fullSupport hC B ℓ hpos) hobs⟩

section pointwise

variable {B : Tree Ω ι acts K} {d : ι}

/-- Disjoint action events at `d`. Source: [[decision-problems-v2]] §2 (action events are
disjoint). Kind: D -/
def DisjointActEv (d : ι) : Prop := ∀ a b : acts d, a ≠ b → Disjoint (actEv d a) (actEv d b)

/-- **The pointwise identity at F3′ points, act form**: the `μ`-weighted indicator of
`λ(ℓ) ⊨ a ∧ O_d` is the sum over node-action-veridical `d`-nodes of the indicator "the path took
the `a`-edge at that node".
Source: [[decision-problems-v2]] Proposition 7 proof, transported from Definition 7 to F3′
Kind: P -/
theorem ind_actEv_eq_sum_navFiber (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) (C : Proc ι acts K) (a : acts d) (ℓ : B.Leaves) :
    (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0) =
      ∑ q ∈ navFiber actEv B d, (if edgeS B q ℓ = some ⟨d, a⟩ then leafLaw C B ℓ else 0) := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have hcw : 0 < chanceWeight B ℓ := Positive.of_leafLaw_pos C hpos
    by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨q₀, ⟨hq₀, hnav⟩, huniq⟩ := h.2 ℓ hcw hobs
      rw [mem_dNodesOn] at hq₀
      obtain ⟨hpt, hsome⟩ := hq₀
      rw [Finset.sum_eq_single q₀]
      · subst hpt
        obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hsome
        have hact : world B ℓ ∈ actEv (pt B q₀) a₀ := hnav ℓ a₀ ha₀
        simp only [edgeS_eq_some_iff, ha₀, Option.some.injEq]
        by_cases hE : a = a₀
        · subst hE; simp [hact, hobs]
        · have hnot : world B ℓ ∉ actEv (pt B q₀) a := fun hc =>
            Finset.disjoint_left.mp (hdisj a a₀ hE) hc hact
          simp [hnot, Ne.symm hE]
      · intro q hq hne
        have : ¬ edgeS B q ℓ = some ⟨d, a⟩ := by
          intro he
          have hq' : q ∈ dNodesOn B d ℓ := by
            rw [mem_dNodesOn]
            exact ⟨pt_eq_of_edgeS B q ℓ he, isSome_of_edgeS B q ℓ he⟩
          exact hne (huniq q ⟨hq', ((mem_navFiber actEv B d q).mp hq).2⟩)
        simp [this]
      · intro hq
        exact absurd ((mem_navFiber actEv B d q₀).mpr ⟨hpt, hnav⟩) hq
    · have hL : ¬ (world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d) := fun hc => hobs hc.2
      rw [if_neg hL]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      rw [mem_navFiber] at hq
      have : ¬ edgeS B q ℓ = some ⟨d, a⟩ := by
        intro he
        have hbelow : ℓ ∈ leavesBelow B q :=
          (mem_leavesBelow B q ℓ).mpr (isSome_of_edgeS B q ℓ he)
        have := h.1 q hq.1 hq.2 ℓ hbelow
        rw [hq.1] at this
        exact hobs this
      simp [this]
  · rw [← hzero]; simp

/-- **The pointwise identity at F3′ points, observation form**: the `μ`-weighted indicator of
`λ(ℓ) ⊨ O_d` is the sum over node-action-veridical `d`-nodes of the indicator "the path passes
that node".
Source: [[decision-problems-v2]] Proposition 7 proof, transported to F3′
Kind: P -/
theorem ind_obs_eq_sum_navFiber (h : ActRecordingStruct obs actEv B d) (C : Proc ι acts K)
    (ℓ : B.Leaves) :
    (if world B ℓ ∈ obs d then leafLaw C B ℓ else 0) =
      ∑ q ∈ navFiber actEv B d, (if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0) := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have hcw : 0 < chanceWeight B ℓ := Positive.of_leafLaw_pos C hpos
    by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨q₀, ⟨hq₀, hnav⟩, huniq⟩ := h.2 ℓ hcw hobs
      rw [mem_dNodesOn] at hq₀
      rw [Finset.sum_eq_single q₀]
      · simp [hobs, hq₀.2]
      · intro q hq hne
        have : ¬ (edgeOf B q ℓ).isSome := by
          intro he
          have hq' : q ∈ dNodesOn B d ℓ := by
            rw [mem_dNodesOn]; exact ⟨((mem_navFiber actEv B d q).mp hq).1, he⟩
          exact hne (huniq q ⟨hq', ((mem_navFiber actEv B d q).mp hq).2⟩)
        simp [this]
      · intro hq
        exact absurd ((mem_navFiber actEv B d q₀).mpr ⟨hq₀.1, hnav⟩) hq
    · rw [if_neg hobs]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      rw [mem_navFiber] at hq
      have : ¬ (edgeOf B q ℓ).isSome := by
        intro he
        have hbelow : ℓ ∈ leavesBelow B q := (mem_leavesBelow B q ℓ).mpr he
        have := h.1 q hq.1 hq.2 ℓ hbelow
        rw [hq.1] at this
        exact hobs this
      simp [this]
  · rw [← hzero]; simp

/-- **The recording lemma at F3′ points** (T7(a); also `dp-referents-cdt`'s C2-1): for every
procedure `C`, `ν_C(a ∧ O_d) = C(d)(a) · ν_C(O_d)`. The real node's draw contributes the factor
`C(d)(a)` once; the mass of the runs reaching a real node is `ν_C(O_d)`.
Source: [[decision-problems-v2]] Remark 3.6 (the recording argument), at F3′-structural points;
`repair/C2.md` C2-L1/C2-1; mandate T7(a)
Kind: P
Fidelity: exact (cross-multiplied; for every procedure)
Hyps: (a) `ActRecordingStruct` (F3′ for every procedure), (a) disjoint action events at `d` -/
theorem nu_actEv_inter_obs_of_struct (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) (C : Proc ι acts K) (a : acts d) :
    nu C B (actEv d a ∩ obs d) = (C d).w a * nu C B (obs d) := by
  have hL : nu C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0 := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  have hR : nu C B (obs d) = ∑ q ∈ navFiber actEv B d,
      ∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0 := by
    rw [nu_eq_sum, Finset.sum_congr rfl (fun ℓ _ => ind_obs_eq_sum_navFiber obs actEv h C ℓ),
      Finset.sum_comm]
  rw [hL, Finset.sum_congr rfl (fun ℓ _ => ind_actEv_eq_sum_navFiber obs actEv h hdisj C a ℓ),
    Finset.sum_comm, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  exact mass_edgeS C B q ((mem_navFiber actEv B d q).mp hq).1 a

/-- A chance-positive leaf with `λ(ℓ) ⊨ a ∧ O_d` drew `a` at some `d`-node (the real one).
Source: none: infrastructure (F3′ + disjointness). Kind: L -/
theorem mem_draws_of_actEv_inter_obs (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) {a : acts d} {ℓ : B.Leaves} (hcw : 0 < chanceWeight B ℓ)
    (hw : world B ℓ ∈ actEv d a ∩ obs d) : (⟨d, a⟩ : Σ e, acts e) ∈ draws B ℓ := by
  rw [Finset.mem_inter] at hw
  obtain ⟨q₀, ⟨hq₀, hnav⟩, -⟩ := h.2 ℓ hcw hw.2
  rw [mem_dNodesOn] at hq₀
  obtain ⟨hpt, hsome⟩ := hq₀
  subst hpt
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hsome
  have hact : world B ℓ ∈ actEv (pt B q₀) a₀ := hnav ℓ a₀ ha₀
  have hE : a = a₀ := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj a a₀ hne) hw.1 hact
  subst hE
  rw [mem_draws_iff_exists_edgeS]
  exact ⟨q₀, (edgeS_eq_some_iff B q₀ ℓ a).mpr ha₀⟩

end pointwise

/-! ## The payoff side: one draw factor erased -/

section reduced

/-- The product of the draw weights on a leaf's path with **one** `⟨d, a⟩`-draw erased (the real
node's factor); a polynomial in the weights of `C`.
Source: mandate T7(a) ("`Q_a` is a polynomial in the weights of `m`")
Kind: D -/
def reducedWeight (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K)
    (ℓ : B.Leaves) : K :=
  (((draws B ℓ).erase ⟨d, a⟩).map fun x => (C x.1).w x.2).prod

/-- `Q_a(C)` on an event `Y`: `∑_{λ(ℓ) ⊨ Y} chanceWeight(ℓ) · reducedWeight(ℓ) · r(ℓ)`.
Source: mandate T7(a) (`Q_a m`)
Kind: D -/
def qSum (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K) (Y : Finset Ω) : K :=
  ∑ ℓ ∈ worldEv B Y, chanceWeight B ℓ * reducedWeight C d a B ℓ * payoff B ℓ

/-- On a leaf that drew `⟨d, a⟩`, the draw weight is `C(d)(a)` times the reduced weight.
Source: none: infrastructure. Kind: L -/
theorem drawsWeight_eq_w_mul_reducedWeight (C : Proc ι acts K) {d : ι} {a : acts d}
    {B : Tree Ω ι acts K} {ℓ : B.Leaves} (hmem : (⟨d, a⟩ : Σ e, acts e) ∈ draws B ℓ) :
    drawsWeight C B ℓ = (C d).w a * reducedWeight C d a B ℓ := by
  unfold drawsWeight reducedWeight
  exact (List.prod_map_erase (fun x : Σ e, acts e => (C x.1).w x.2) hmem).symm

/-- **The payoff factorisation at F3′ points**: `𝔼_C[r · 1_{a ∧ O_d}] = C(d)(a) · Q_a(C)` for
every procedure `C`.
Source: mandate T7(a) ("`paySum … = m.w a * Q_a m`")
Kind: P
Fidelity: exact
Hyps: (a) `ActRecordingStruct`, (a) disjoint action events -/
theorem paySum_eq_w_mul_qSum {B : Tree Ω ι acts K} {d : ι} (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) (C : Proc ι acts K) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) = (C d).w a * qSum C d a B (actEv d a ∩ obs d) := by
  unfold paySum qSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hw : world B ℓ ∈ actEv d a ∩ obs d := by
    unfold worldEv at hℓ; exact (Finset.mem_filter.mp hℓ).2
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hcw | hcw
  · rw [leafLaw_eq_chanceWeight_mul_drawsWeight,
      drawsWeight_eq_w_mul_reducedWeight C (mem_draws_of_actEv_inter_obs obs actEv h hdisj hcw hw)]
    ring
  · rw [leafLaw_eq_chanceWeight_mul_drawsWeight, ← hcw]; ring

end reduced

/-! ## The `ε`-polynomials -/

section poly

/-- `leafLawPoly` as `C(chanceWeight) · ∏_{draws} trembleW`.
Source: none: infrastructure (the polynomial form of `leafLaw_eq_chanceWeight_mul_drawsWeight`)
Kind: L -/
theorem leafLawPoly_eq_C_mul_prod (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLawPoly C B ℓ =
      Polynomial.C (chanceWeight B ℓ) * ((draws B ℓ).map fun x => trembleW C x.1 x.2).prod
  | .leaf _ _, _ => by simp [leafLawPoly, chanceWeight, draws]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_chance, draws_chance, Polynomial.C_mul]
      rw [leafLawPoly_eq_C_mul_prod C (child i) ℓ]; ring
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPoly, chanceWeight_decision, draws_decision, List.map_cons,
        List.prod_cons]
      rw [leafLawPoly_eq_C_mul_prod C (child a) ℓ]; ring

/-- `Q_a` as a polynomial in `ε` (the trembled `reducedWeight`).
Source: mandate T7(b)
Kind: D -/
noncomputable def qPoly (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K)
    (Y : Finset Ω) : Polynomial K :=
  ∑ ℓ ∈ worldEv B Y, Polynomial.C (chanceWeight B ℓ) *
    (((draws B ℓ).erase ⟨d, a⟩).map fun x => trembleW C x.1 x.2).prod * Polynomial.C (payoff B ℓ)

/-- `trembleW` at `ε = 0` is the weight. Source: none: infrastructure. Kind: L -/
theorem trembleW_eval_zero (C : Proc ι acts K) (e : ι) (b : acts e) :
    (trembleW C e b).eval 0 = (C e).w b := by
  simp [trembleW]

/-- The constant coefficient of `qPoly` is `qSum`.
Source: none: infrastructure. Kind: L -/
theorem coeff_zero_qPoly (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K)
    (Y : Finset Ω) : (qPoly C d a B Y).coeff 0 = qSum C d a B Y := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold qPoly qSum reducedWeight
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
    Polynomial.eval_list_prod, List.map_map]
  congr 2
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  exact trembleW_eval_zero C x.1 x.2

/-- **`payPoly (a ∧ O_d) = trembleW(d, a) · qPoly`** at F3′ points (the real node's factor pulled
out at the polynomial level).
Source: mandate T7(b)
Kind: P
Hyps: (a) `ActRecordingStruct`, (a) disjoint action events -/
theorem payPoly_eq_trembleW_mul_qPoly {B : Tree Ω ι acts K} {d : ι}
    (h : ActRecordingStruct obs actEv B d) (hdisj : DisjointActEv actEv d) (C : Proc ι acts K)
    (a : acts d) :
    payPoly C B (actEv d a ∩ obs d) = trembleW C d a * qPoly C d a B (actEv d a ∩ obs d) := by
  unfold payPoly qPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hw : world B ℓ ∈ actEv d a ∩ obs d := by
    unfold worldEv at hℓ; exact (Finset.mem_filter.mp hℓ).2
  rw [leafLawPoly_eq_C_mul_prod]
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hcw | hcw
  · rw [← List.prod_map_erase (fun x : Σ e, acts e => trembleW C x.1 x.2)
      (mem_draws_of_actEv_inter_obs obs actEv h hdisj hcw hw)]
    ring
  · rw [← hcw]; simp

/-- **`nuPoly (a ∧ O_d) = trembleW(d, a) · nuPoly O_d`** at F3′ points: the recording lemma holds
for every tremble, hence as an identity of polynomials in `ε`.
Source: mandate T7(b)
Kind: P
Hyps: (a) `ActRecordingStruct`, (a) disjoint action events -/
theorem nuPoly_eq_trembleW_mul_nuPoly_obs {B : Tree Ω ι acts K} {d : ι}
    (h : ActRecordingStruct obs actEv B d) (hdisj : DisjointActEv actEv d) (C : Proc ι acts K)
    (a : acts d) :
    nuPoly C B (actEv d a ∩ obs d) = trembleW C d a * nuPoly C B (obs d) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Icc_infinite (zero_lt_one' K))
  intro ε hε
  simp only [Set.mem_setOf_eq]
  rw [Polynomial.eval_mul, eval_nuPoly C B _ ε hε.1 hε.2, eval_trembleW C d a ε hε.1 hε.2,
    eval_nuPoly C B _ ε hε.1 hε.2]
  exact nu_actEv_inter_obs_of_struct obs actEv h hdisj (tremble C ε hε.1 hε.2) a

/-- Every act event is tremble-realizable within `O_d` at an F3′ point whose observation is.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_actEv_inter_obs_ne_zero {B : Tree Ω ι acts K} {d : ι}
    (h : ActRecordingStruct obs actEv B d) (hdisj : DisjointActEv actEv d) (C : Proc ι acts K)
    (hO : nuPoly C B (obs d) ≠ 0) (a : acts d) : nuPoly C B (actEv d a ∩ obs d) ≠ 0 := by
  rw [nuPoly_eq_trembleW_mul_nuPoly_obs obs actEv h hdisj C a]
  exact mul_ne_zero (trembleW_ne_zero C d a) hO

/-- The coefficient of `p · q` at the order of `p` is `trailingCoeff p · q(0)`.
Source: none: infrastructure. Kind: L -/
theorem coeff_mul_natTrailingDegree_left (p q : Polynomial K) :
    (p * q).coeff p.natTrailingDegree = p.trailingCoeff * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (p.natTrailingDegree, 0)]
  · rfl
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have hi : i < p.natTrailingDegree := by
      rcases Nat.lt_or_ge i p.natTrailingDegree with hlt | hge
      · exact hlt
      · exfalso; apply hne
        have : i = p.natTrailingDegree := by omega
        subst this
        have : j = 0 := by omega
        subst this; rfl
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  · intro hn; exact absurd (Finset.mem_antidiagonal.mpr (Nat.add_zero _)) hn

/-- The order of `p · q` is the order of `p` when `q(0) ≠ 0`.
Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_mul_of_coeff_zero_ne_zero {p q : Polynomial K} (hp : p ≠ 0)
    (hq : q.coeff 0 ≠ 0) : (p * q).natTrailingDegree = p.natTrailingDegree := by
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, Polynomial.coeff_zero])
  rw [Polynomial.natTrailingDegree_mul hp hq0,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hq), Nat.add_zero]

/-- **T7(b): the tremble-pinned act value is `Q_a(m) / R(m)`** for every label `m` — including
`m(a) = 0`, where both `ε`-polynomials have order one and the ratio of their `ε¹`-coefficients is
the same quotient — under the standing hypothesis `R(m) = ν_{C[d↦m]}(O_d) > 0`. C2-7's "ratio of
polynomials with positive denominator", proved from the tree.
Source: `repair/C2.md` line 72 (C2-7); mandate T7(b)
Kind: P
Fidelity: exact (for the algebraic `limitVal`)
Hyps: (a) `ActRecordingStruct` (F3′ for every procedure), (a) disjoint action events,
(a) `0 < ν_{C[d↦m]}(O_d)` (the standing hypothesis at this `m`) -/
theorem r3Val_eq_qSum_div {B : Tree Ω ι acts K} {d : ι} (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) (C : Proc ι acts K) (m : FinDistr K (acts d)) (a : acts d)
    (hR : 0 < nu (C.deviate d m) B (obs d)) :
    r3Val obs actEv C B d m a =
      qSum (C.deviate d m) d a B (actEv d a ∩ obs d) / nu (C.deviate d m) B (obs d) := by
  unfold r3Val limitVal
  set C' := C.deviate d m with hC'
  have hN0 : (nuPoly C' B (obs d)).coeff 0 ≠ 0 := by
    rw [coeff_zero_nuPoly]; exact hR.ne'
  have htW : trembleW C' d a ≠ 0 := trembleW_ne_zero C' d a
  rw [nuPoly_eq_trembleW_mul_nuPoly_obs obs actEv h hdisj C' a,
    payPoly_eq_trembleW_mul_qPoly obs actEv h hdisj C' a,
    natTrailingDegree_mul_of_coeff_zero_ne_zero htW hN0,
    coeff_mul_natTrailingDegree_left, coeff_mul_natTrailingDegree_left, coeff_zero_qPoly,
    coeff_zero_nuPoly]
  have htc : (trembleW C' d a).trailingCoeff ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr htW
  rw [mul_div_mul_left _ _ htc]

end poly

end Cleanroom.Decision.DpDutchBook
