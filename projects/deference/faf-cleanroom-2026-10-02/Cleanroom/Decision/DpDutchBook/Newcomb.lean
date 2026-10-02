import Cleanroom.Decision.DpDutchBook.MsrValues
import Cleanroom.Decision.DpCalibration.Mugging

/-!
# T3–T4(a): the Definition-6 inversion on opaque Newcomb, parameters free

On `opaqueNewcomb p L S` (a predictor node upstream samples `C(d)`, the box is filled according
to the sample with probability `p`, then the live node is queried; `O_d = ⊤`; `Act2.a` = one-box,
`Act2.b` = two-box), with `q := C(d)(one)`, everything below is a closed form **proved from the
tree** (eight-leaf sums), with `(p, L, S, q)` free:

* `opaqueE` — the strictly calibrated act values `e(one) = L(pq + (1−p)(1−q))`,
  `e(two) = e(one) + S` (at positive acts).
* `opaqueR1State` — the deviation referent `V_B(C[d ↦ a])`: `(Lp, L(1−p) + S)`.
* `opaqueR3` — the tremble-pinned value at the label (`r3Val` at `C(d)`): `= e` at every `q`,
  boundary included (`r3Val_eq_qSum_div` on this tree; `ActRecordingStruct` and disjointness
  proved).
* The **book gap** `Δ_c(a) := C(d)(a) · |c(a) − e(a)|` (the quantity T2's threshold compares
  with `2δ`): **`Δ_{R1}(one) = q·L·(1−q)·(2p−1)`** for `p ≥ ½`, and the same for `two`; the two
  parametrizations of the critic's C2 (`2q(1−q)` at `(¾, 4, 1)`, `Lq(1−q)` at `p = 1`) are
  instances; **`Δ_{R3} = 0`** at positive acts (the forcing-type referent equals conditioning —
  unbookable under Definition 6). At the deterministic labels the taken act has `Δ = 0`.
* The argmax lemmas: at a properly mixed label the R1-state argmax is `{one}` (when
  `S < L(2p−1)`) and the conditioning/forcing argmax is `{two}` (`S > 0`), so no properly mixed
  label is approved by either cf's own theory (P12-5's advice-reading clause).
* T4(a): the forcing cf at mixed `q` is unbookable yet disapproves the label ("⇐" of the
  reviewer's biconditional fails); "bookable ⇒ disapproved" holds for the R1-state cf **iff**
  `S ≠ L(2p−1)` — at `S = L(2p−1)` the R1-state values tie and a bookable mixed label is
  approved (`opaque_bookable_and_approved`, a new finding).

The shared-seed (6′) side is `NewcombSeed.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- **Approval of a label by a value function** (Definition 18's support-in-argmax for a
`SupposedVal`): every supported act maximises `c`.
Source: [[decision-problems-v2]] §4 Definition 18 (`supp C(d) ⊆ argmax`); P12-5 ("the booked
cf's own `T_CDT`")
Kind: D
Fidelity: variant: cf reduced to its act values -/
def ApprovedBy {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Type} [Fintype A]
    (m : FinDistr K A) (c : A → K) : Prop :=
  ∀ x, 0 < m.w x → ∀ y, c y ≤ c x

/-- **The book gap** `Δ_c(a) := m(a) · |c(a) − e(a)|` of a label `m` between a supposed value `c`
and the calibrated value `e` at the act `a` (P12's `Δ`).
Source: `sl-workflow/notes/repair/P12.md` Setting (`Δ := P_{s_d}(a) |c − e|`)
Kind: D
Fidelity: variant: cf reduced to its act values -/
def bookGap {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Type} [Fintype A]
    (m : FinDistr K A) (c e : A → K) (a : A) : K :=
  m.w a * |c a - e a|

section opaqueTree

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- Sums over the eight leaves of opaque Newcomb. Source: none: infrastructure. Kind: L -/
theorem opaque_sum {M : Type} [AddCommMonoid M] (f : (opaqueNewcomb p h0 h1 L S).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ i : Fin 2, ∑ l : Act2, f ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ := by
  unfold opaqueNewcomb at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- `ν(act = a) = C(d)(a)` on opaque Newcomb (the live draw's marginal is the label).
Source: none: infrastructure. Kind: L -/
theorem opaque_nu_act (a : Act2) : nu C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, opaque_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  cases a
  · simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, FinDistr.coin]
    linear_combination (C ()).w Act2.a * hs
  · simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, FinDistr.coin]
    linear_combination (C ()).w Act2.b * hs

/-- `𝔼[r · 1_{one}] = q · L · (pq + (1−p)(1−q))` on opaque Newcomb.
Source: none: infrastructure. Kind: L -/
theorem opaque_paySum_a :
    paySum C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .a) =
      (C ()).w .a * (L * (p * (C ()).w .a + (1 - p) * (C ()).w .b)) := by
  rw [paySum_eq_sum_ite, opaque_sum]
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaquePay, opaqueFill,
    FinDistr.coin]
  ring

/-- `𝔼[r · 1_{two}] = (1−q) · (L(pq + (1−p)(1−q)) + S)` on opaque Newcomb.
Source: none: infrastructure. Kind: L -/
theorem opaque_paySum_b :
    paySum C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .b) =
      (C ()).w .b * (L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) + S) := by
  rw [paySum_eq_sum_ite, opaque_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaquePay, opaqueFill,
    FinDistr.coin]
  linear_combination (C ()).w Act2.b * S * hs

/-- The strictly calibrated act value `e(a) = 𝔼_μ[r ∣ a ∧ O_d]` on opaque Newcomb (`O_d = ⊤`).
Source: `sl-workflow/notes/repair/P12.md` Setting (`e := V_{s_d}(a)`); C2-16′ (`edt(one)`)
Kind: D -/
noncomputable def opaqueE (a : Act2) : ℚ := condExp C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a ∩ opaqueObs ())

/-- **`e(one) = L(pq + (1−p)(1−q))`** at a positive one-box weight.
Source: C2-16′ (`edt(one) = 2q + 1` at `(¾, 4, 1)`); mandate T3
Kind: P
Fidelity: exact
Hyps: (a) `0 < q` (the guard of the conditional) -/
theorem opaqueE_a (hq : 0 < (C ()).w .a) :
    opaqueE p h0 h1 L S C .a = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) := by
  unfold opaqueE condExp
  rw [opaqueObs, Finset.inter_univ, opaque_paySum_a, opaque_nu_act]
  field_simp

/-- **`e(two) = e(one) + S`** at a positive two-box weight.
Source: C2-16′; mandate T3
Kind: P
Fidelity: exact
Hyps: (a) `0 < 1 − q` -/
theorem opaqueE_b (hq : 0 < (C ()).w .b) :
    opaqueE p h0 h1 L S C .b = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) + S := by
  unfold opaqueE condExp
  rw [opaqueObs, Finset.inter_univ, opaque_paySum_b, opaque_nu_act]
  field_simp

/-- The deviation referent R1-state on opaque Newcomb: `V_B(C[d ↦ a])` (`O_d = ⊤`, so the
`O_d`-conditioned deviation value is the all-instance deviation value).
Source: `repair/C2.md` C2-16′ ("the deviation referent R1-state"); mandate §3.2 (`r1State`)
Kind: D -/
def opaqueR1State (a : Act2) : ℚ := value (C.deviatePure () a) (opaqueNewcomb p h0 h1 L S)

/-- **`R1-state(one) = Lp`**: the deterministic one-boxer's value.
Source: C2-16′ (`R1-state(one) = 3` at `(¾, 4)`); mandate T3
Kind: P
Fidelity: exact -/
theorem opaqueR1State_a : opaqueR1State p h0 h1 L S C .a = L * p := by
  unfold opaqueR1State value
  rw [Proc.deviatePure, deviate_unit, opaque_sum]
  simp [Fin.sum_univ_two, opaqueNewcomb, opaquePay, opaqueFill, FinDistr.coin, FinDistr.pure]
  ring

/-- **`R1-state(two) = L(1−p) + S`**: the deterministic two-boxer's value.
Source: C2-16′ (`R1-state = (3, 2)` at `(¾, 4, 1)`); mandate T3
Kind: P
Fidelity: exact -/
theorem opaqueR1State_b : opaqueR1State p h0 h1 L S C .b = L * (1 - p) + S := by
  unfold opaqueR1State value
  rw [Proc.deviatePure, deviate_unit, opaque_sum]
  simp [Fin.sum_univ_two, opaqueNewcomb, opaquePay, opaqueFill, FinDistr.coin, FinDistr.pure]
  ring

/-! ### F3′ on opaque Newcomb, and the tremble-pinned values -/

/-- Opaque Newcomb's action events are disjoint. Source: none: infrastructure. Kind: L -/
theorem opaque_disjointActEv : DisjointActEv opaqueActEv () := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [opaqueActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (hw.symm.trans hw')

/-- The live nodes of opaque Newcomb are node-action-veridical, the predictor node is not:
**F3′ holds structurally** (every chance-positive leaf passes exactly one node-action-veridical
`d`-node, its own live node; `O_d = ⊤` makes subtree-veridicality trivial).
Source: dp-sl-2-041 (opaque Newcomb: "predictor node upstream sampling `C(d)`"); `dp-core-tree`'s
`opaqueNewcomb_actRecording`; mandate T3
Kind: P
Fidelity: exact -/
theorem opaque_actRecordingStruct : ActRecordingStruct opaqueObs opaqueActEv (opaqueNewcomb p h0 h1 L S) () := by
  refine ⟨fun _ _ _ ℓ _ => Finset.mem_univ _, fun ℓ hcw _ => ?_⟩
  obtain ⟨s, i, l, ⟨⟩⟩ := ℓ
  -- the live node on the path
  refine ⟨some ⟨s, ⟨i, none⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_dNodesOn]
    exact ⟨rfl, by simp [opaqueNewcomb, edgeOf]⟩
  · intro ℓ' a he
    obtain ⟨s', i', l', ⟨⟩⟩ := ℓ'
    by_cases hs : s' = s
    · subst hs
      by_cases hi : i' = i
      · subst hi
        simp [opaqueNewcomb] at he
        subst he
        simp [opaqueNewcomb, opaqueActEv]
      · simp [opaqueNewcomb, hi] at he
    · simp [opaqueNewcomb, hs] at he
  · rintro q ⟨hq, hnav⟩
    rw [mem_dNodesOn] at hq
    obtain ⟨-, hsome⟩ := hq
    -- the only other `d`-node on the path is the predictor node, which is not veridical
    rcases q with _ | ⟨s', i', q'⟩
    · exfalso
      -- the predictor node draws `s` while the world records `l`: take the leaf with `l ≠ s`
      have h1 := hnav ⟨s, ⟨i, ⟨Act2.a, ()⟩⟩⟩ s (by simp [opaqueNewcomb])
      have h2 := hnav ⟨s, ⟨i, ⟨Act2.b, ()⟩⟩⟩ s (by simp [opaqueNewcomb])
      simp [opaqueNewcomb, opaqueActEv] at h1 h2
      cases s <;> simp_all
    · rcases q' with _ | ⟨a', q''⟩
      · -- a live node: must be on the path, so `(s', i') = (s, i)`
        by_cases hs : s = s'
        · subst hs
          by_cases hi : i = i'
          · subst hi; rfl
          · simp [opaqueNewcomb, hi] at hsome
        · simp [opaqueNewcomb, hs] at hsome
      · exact q''.elim

/-- `Q_one(m) = L(p·m(one) + (1−p)·m(two))` on opaque Newcomb: the reduced draw weight of a live
one-box leaf is the predictor's draw weight.
Source: none: infrastructure. Kind: L -/
theorem opaque_qSum_a :
    qSum C () .a (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .a ∩ opaqueObs ()) =
      L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) := by
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, opaque_sum]
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaqueObs, opaquePay,
    opaqueFill, FinDistr.coin, List.erase_cons]
  ring

/-- `Q_two(m) = L(p·m(one) + (1−p)·m(two)) + S` on opaque Newcomb.
Source: none: infrastructure. Kind: L -/
theorem opaque_qSum_b :
    qSum C () .b (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .b ∩ opaqueObs ()) =
      L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) + S := by
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, opaque_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaqueObs, opaquePay,
    opaqueFill, FinDistr.coin, List.erase_cons]
  linear_combination S * hs

/-- The tremble-pinned act value at the label on opaque Newcomb (the R3 referent).
Source: `repair/C2.md` C2-16′ (R3); mandate §3.2 (`r3`)
Kind: D
Fidelity: variant: limit taken algebraically -/
noncomputable def opaqueR3 (a : Act2) : ℚ := r3Val opaqueObs opaqueActEv C (opaqueNewcomb p h0 h1 L S) () (C ()) a

/-- **`R3(one) = L(pq + (1−p)(1−q))` at every label**, boundary included.
Source: C2-17′ ("R3 agrees with R2-real at nulled acts too"); mandate T3 ("`r3 = e` at interior
`q` (and at `q ∈ {0,1}` the tremble-limit values)")
Kind: P
Fidelity: exact -/
theorem opaqueR3_a : opaqueR3 p h0 h1 L S C .a = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) := by
  unfold opaqueR3
  rw [r3Val_eq_qSum_div opaqueObs opaqueActEv (opaque_actRecordingStruct p h0 h1 L S)
    (opaque_disjointActEv) C (C ()) .a (by rw [Proc.deviate_self, opaqueObs, nu_univ]; exact one_pos)]
  rw [Proc.deviate_self, opaqueObs, nu_univ, div_one, ← opaqueObs, opaque_qSum_a]

/-- **`R3(two) = L(pq + (1−p)(1−q)) + S` at every label.**
Source: C2-17′ (`R3(two) = 4` at `δ_one`, `(¾, 4, 1)`); mandate T3
Kind: P
Fidelity: exact -/
theorem opaqueR3_b :
    opaqueR3 p h0 h1 L S C .b = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) + S := by
  unfold opaqueR3
  rw [r3Val_eq_qSum_div opaqueObs opaqueActEv (opaque_actRecordingStruct p h0 h1 L S)
    (opaque_disjointActEv) C (C ()) .b (by rw [Proc.deviate_self, opaqueObs, nu_univ]; exact one_pos)]
  rw [Proc.deviate_self, opaqueObs, nu_univ, div_one, ← opaqueObs, opaque_qSum_b]

/-- **`R3 = e` at positive acts** (the forcing-type referent equals conditioning under
Definition 6 at this F3′ point; C2-A′ on opaque Newcomb).
Source: C2-16′ ("under Definition 6 at F3′-structural points such a cf is calibrated to neither
forcing-type referent"); S9
Kind: C
Hyps: (a) the act's weight positive -/
theorem opaqueR3_eq_opaqueE (a : Act2) (hq : 0 < (C ()).w a) :
    opaqueR3 p h0 h1 L S C a = opaqueE p h0 h1 L S C a := by
  cases a
  · rw [opaqueR3_a, opaqueE_a p h0 h1 L S C hq]
  · rw [opaqueR3_b, opaqueE_b p h0 h1 L S C hq]

/-! ### The book gaps -/

/-- **`Δ_{R1}(one) = q · L · (1−q) · (2p−1)`** for `p ≥ ½`, `L ≥ 0`: the deviation cf's gap to
conditioning at the one-box act, in the free parameters. The critic's two parametrizations are
`opaque_gap_r1_a_inst` below.
Source: C2-16′ ("`q(3 − (2q+1)) = 2q(1−q)`" at `(¾, 4)`); S12; sl-amendments critic C2 (HIGH);
mandate T3
Kind: P
Fidelity: exact (`Δ` derived from `condExp` and `value`, never asserted)
Hyps: (a) `0 < q` (the guard of `e`), `½ ≤ p`, `0 ≤ L` -/
theorem opaque_gap_r1_a (hq : 0 < (C ()).w .a) (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) .a =
      (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) := by
  unfold bookGap
  rw [opaqueR1State_a, opaqueE_a p h0 h1 L S C hq]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  rw [hb]
  have e : L * p - L * (p * (C ()).w .a + (1 - p) * (1 - (C ()).w .a)) =
      L * (1 - (C ()).w .a) * (2 * p - 1) := by ring
  rw [e, abs_of_nonneg (mul_nonneg (mul_nonneg hL (by linarith [(C ()).w_le_one .a])) (by linarith))]
  ring

/-- **`Δ_{R1}(two) = q · L · (1−q) · (2p−1)`** for `p ≥ ½`, `L ≥ 0` — the same gap at the two-box
act.
Source: mandate T3 (the mirror case)
Kind: P
Fidelity: exact
Hyps: (a) `0 < 1 − q`, `½ ≤ p`, `0 ≤ L` -/
theorem opaque_gap_r1_b (hq : 0 < (C ()).w .b) (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) .b =
      (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) := by
  unfold bookGap
  rw [opaqueR1State_b, opaqueE_b p h0 h1 L S C hq]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  rw [hb]
  have e : L * (1 - p) + S - (L * (p * (C ()).w .a + (1 - p) * (1 - (C ()).w .a)) + S) =
      -(L * (C ()).w .a * (2 * p - 1)) := by ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hL ((C ()).nonneg .a)) (by linarith))]
  ring

/-- **The critic's two parametrizations as instances**: at `(p, L) = (¾, 4)` the gap is
`2q(1−q)`; at `p = 1` it is `Lq(1−q)`. SL-23(b)(iii) spliced the two; here each is an instance
of one closed form.
Source: sl-amendments line 3 (critic C2, HIGH); mandate §5.1
Kind: N+
Hyps: (a) as `opaque_gap_r1_a` -/
theorem opaque_gap_r1_a_inst (hq : 0 < (C ()).w .a) :
    bookGap (C ()) (opaqueR1State (3 / 4) (by norm_num) (by norm_num) 4 S C)
        (opaqueE (3 / 4) (by norm_num) (by norm_num) 4 S C) .a =
      2 * (C ()).w .a * (1 - (C ()).w .a) ∧
    ∀ (L : ℚ), 0 ≤ L →
      bookGap (C ()) (opaqueR1State 1 (by norm_num) le_rfl L S C)
          (opaqueE 1 (by norm_num) le_rfl L S C) .a =
        L * (C ()).w .a * (1 - (C ()).w .a) := by
  constructor
  · rw [opaque_gap_r1_a _ _ _ _ _ C hq (by norm_num) (by norm_num)]; ring
  · intro L hL
    rw [opaque_gap_r1_a _ _ _ _ _ C hq (by norm_num) hL]; ring

/-- **`Δ_{R3}(a) = 0` at positive acts**: the forcing-type referent is unbookable under
Definition 6.
Source: C2-16′ ("spares classical CDT"); S12; mandate T3 (`Δ_{R2} = Δ_{R3} = 0`)
Kind: P
Fidelity: exact
Hyps: (a) the act's weight positive -/
theorem opaque_gap_r3 (a : Act2) (hq : 0 < (C ()).w a) :
    bookGap (C ()) (opaqueR3 p h0 h1 L S C) (opaqueE p h0 h1 L S C) a = 0 := by
  unfold bookGap
  rw [opaqueR3_eq_opaqueE p h0 h1 L S C a hq, sub_self, abs_zero, mul_zero]

/-- **At the deterministic fixed points the taken act has `Δ_{R1} = 0`**: the one-boxer (`q = 1`)
at `one`, the two-boxer (`q = 0`) at `two`.
Source: P12-5 ("at opaque Newcomb's two deterministic fixed points … the taken act has `Δ = 0`");
mandate T3 (fixed points)
Kind: P
Hyps: (a) `½ ≤ p`, `0 ≤ L`; the label deterministic -/
theorem opaque_gap_r1_fixed (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    ((C ()).w .a = 1 →
      bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) .a = 0) ∧
    ((C ()).w .b = 1 →
      bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) .b = 0) := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  constructor
  · intro hq
    rw [opaque_gap_r1_a p h0 h1 L S C (by rw [hq]; exact one_pos) hp hL, hq]; ring
  · intro hq
    rw [opaque_gap_r1_b p h0 h1 L S C (by rw [hq]; exact one_pos) hp hL]
    have : (C ()).w .a = 0 := by linarith
    rw [this]; ring

/-! ### Argmaxes: P12-5's advice-reading clause and T4(a) -/

/-- The R1-state argmax is `{one}` when `S < L(2p−1)`.
Source: P12-5 ("strict argmaxes: … one for deviation"); mandate T3
Kind: P
Hyps: (a) `S < L(2p−1)` (at `(¾, 4, 1)`: `1 < 2`) -/
theorem opaqueR1State_b_lt_a (hS : S < L * (2 * p - 1)) :
    opaqueR1State p h0 h1 L S C .b < opaqueR1State p h0 h1 L S C .a := by
  rw [opaqueR1State_a, opaqueR1State_b]; linarith

/-- The conditioning (= forcing, R3) argmax is `{two}` when `S > 0`.
Source: P12-5 ("two for forcing"); mandate T3
Kind: P
Hyps: (a) `0 < S`, both weights positive -/
theorem opaqueE_a_lt_b (hS : 0 < S) (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    opaqueE p h0 h1 L S C .a < opaqueE p h0 h1 L S C .b := by
  rw [opaqueE_a p h0 h1 L S C hqa, opaqueE_b p h0 h1 L S C hqb]; linarith

/-- **No properly mixed label is approved by the R1-state cf** (its argmax is `{one}`).
Source: P12-5; C2-16′ ("at a properly mixed label the booked cf's own `T_CDT` disapproves that
label"); mandate T3
Kind: P
Hyps: (a) both weights positive, `S < L(2p−1)` -/
theorem opaque_r1_disapproves_mixed (_hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b)
    (hS : S < L * (2 * p - 1)) : ¬ ApprovedBy (C ()) (opaqueR1State p h0 h1 L S C) := by
  intro h
  have := h .b hqb .a
  exact absurd this (not_le.mpr (opaqueR1State_b_lt_a p h0 h1 L S C hS))

/-- **No properly mixed label is approved by the forcing-type (R3) cf** (its argmax is `{two}`).
Source: P12-5; mandate T3
Kind: P
Hyps: (a) both weights positive, `0 < S` -/
theorem opaque_r3_disapproves_mixed (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hS : 0 < S) :
    ¬ ApprovedBy (C ()) (opaqueR3 p h0 h1 L S C) := by
  intro h
  have := h .a hqa .b
  rw [opaqueR3_eq_opaqueE p h0 h1 L S C .a hqa, opaqueR3_eq_opaqueE p h0 h1 L S C .b hqb] at this
  exact absurd this (not_le.mpr (opaqueE_a_lt_b p h0 h1 L S C hS hqa hqb))

/-- **T4(a): "unbookable ⇒ approved" fails** (the "⇐" of the reviewer's "bookable iff not
approved"): at a properly mixed label the forcing-type cf has `Δ = 0` at both acts, yet
disapproves the label.
Source: `repair/P12.md` line 15 (P12-5: "the converse fails on the reviewer's own table (forcing
cf under Definition 6 at mixed `q`: unbookable, `Δ = 0`, yet disapproved)"); mandate T4(a)
Kind: N+
Fidelity: exact
Hyps: (a) both weights positive, `0 < S` -/
theorem opaque_forcing_unbookable_disapproved (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b)
    (hS : 0 < S) :
    (∀ a, bookGap (C ()) (opaqueR3 p h0 h1 L S C) (opaqueE p h0 h1 L S C) a = 0) ∧
      ¬ ApprovedBy (C ()) (opaqueR3 p h0 h1 L S C) := by
  refine ⟨fun a => opaque_gap_r3 p h0 h1 L S C a ?_, opaque_r3_disapproves_mixed p h0 h1 L S C hqa hqb hS⟩
  cases a <;> assumption

/-- **The surviving neighbour "bookable ⇒ disapproved" on opaque Newcomb, for the R1-state cf,
under `S ≠ L(2p−1)`**: a positive gap at some act forces a properly mixed label with
`L(2p−1) ≠ 0`, where the R1-state values differ, so the two-element support is not inside the
argmax.
Source: P12-5 ("bookable ⇒ not approved: True"); mandate T4 (the surviving neighbour)
Kind: P
Hyps: (a) `½ ≤ p`, `0 ≤ L`, `S ≠ L(2p−1)` -/
theorem opaque_bookable_imp_disapproved (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) (hS : S ≠ L * (2 * p - 1))
    (a : Act2) (hgap : 0 < bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) a) :
    ¬ ApprovedBy (C ()) (opaqueR1State p h0 h1 L S C) := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hpos : 0 < (C ()).w a := by
    unfold bookGap at hgap
    exact pos_of_mul_pos_left hgap (abs_nonneg _) |> fun h => by
      rcases lt_or_eq_of_le ((C ()).nonneg a) with h' | h'
      · exact h'
      · rw [← h'] at hgap; simp at hgap
  have hform : bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) a =
      (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) := by
    cases a
    · exact opaque_gap_r1_a p h0 h1 L S C hpos hp hL
    · exact opaque_gap_r1_b p h0 h1 L S C hpos hp hL
  rw [hform] at hgap
  have hqa : 0 < (C ()).w .a := by
    rcases lt_or_eq_of_le ((C ()).nonneg .a) with h | h
    · exact h
    · rw [← h] at hgap; simp at hgap
  have hqb : 0 < (C ()).w .b := by
    rcases lt_or_eq_of_le ((C ()).nonneg .b) with h | h
    · exact h
    · have : (C ()).w .a = 1 := by linarith
      rw [this] at hgap; simp at hgap
  have hne : opaqueR1State p h0 h1 L S C .a ≠ opaqueR1State p h0 h1 L S C .b := by
    rw [opaqueR1State_a, opaqueR1State_b]
    intro h; apply hS; linarith
  intro happ
  have h1 := happ .a hqa .b
  have h2 := happ .b hqb .a
  exact hne (le_antisymm h2 h1)

/-- **The unqualified "bookable ⇒ disapproved" fails at `S = L(2p−1)`** (new finding): at
`(p, L, S) = (¾, 4, 2)` and the label `q = ½`, the R1-state gap at `one` is `½ > 0` — the label
is bookable — yet the R1-state values tie (`3 = 3`) and the label is approved.
Source: P12-5 (the neighbour "bookable ⇒ not approved" is stated for `(¾, 4, 1)` only); mandate
T4 (the surviving neighbour), refined
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem opaque_bookable_and_approved :
    0 < bookGap (procQ (1 / 2) (by norm_num) (by norm_num) ())
        (opaqueR1State (3 / 4) (by norm_num) (by norm_num) 4 2 (procQ (1 / 2) (by norm_num) (by norm_num)))
        (opaqueE (3 / 4) (by norm_num) (by norm_num) 4 2 (procQ (1 / 2) (by norm_num) (by norm_num))) .a ∧
    ApprovedBy (procQ (1 / 2) (by norm_num) (by norm_num) ())
      (opaqueR1State (3 / 4) (by norm_num) (by norm_num) 4 2
        (procQ (1 / 2) (by norm_num) (by norm_num))) := by
  constructor
  · rw [opaque_gap_r1_a _ _ _ _ _ _ (by simp [procQ]) (by norm_num) (by norm_num)]
    simp [procQ]; norm_num
  · intro x _ y
    rw [show opaqueR1State (3 / 4) (by norm_num) (by norm_num) 4 2
        (procQ (1 / 2) (by norm_num) (by norm_num)) = fun _ => 3 by
      funext z; cases z
      · rw [opaqueR1State_a]; norm_num
      · rw [opaqueR1State_b]; norm_num]

end opaqueTree

end Cleanroom.Decision.DpDutchBook
