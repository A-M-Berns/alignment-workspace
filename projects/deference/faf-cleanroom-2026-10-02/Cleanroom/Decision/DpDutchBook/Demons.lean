import Cleanroom.Decision.DpDutchBook.NewcombSeed
import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Miniature

/-!
# T10: Skyrms's Mean Demon and Nice Demon — a perfect demon sampling the label

Both demons live on one tree shape, Remark 4.3's miniature with **diagonal** payoffs: a
hypothetical query of `d` (the demon's sample `s`) followed by the live query `l`, paying `u` on
`(1, 1)`, `v` on `(2, 2)` and `0` off the diagonal (`diagDemon u v`). Nice Demon: `(u, v) = (1, 2)`;
Mean Demon: `(−50, −100)`. Everything is computed with `(u, v)` free and `q := C(d)(1)`.

* **Definition 6** (the sampler): `e(1) = u·q`, `e(2) = v·(1−q)` (`diag_e_a/_b`), `V_B(q) = uq² +
  v(1−q)²` (`diag_value`; Nice Demon `3q² − 4q + 2`); a properly mixed label ties iff
  `q = v/(u+v)` (`diag_tie_iff`; `2/3` for both demons — the miniature's phenomenon with these
  payoffs); under the tremble of `δ₁` the values are `(u(1 − ε/2), v·ε/2)` (`diag_tremble_e`).
* **T10(b), the N+ the plan wants**: **`δ₁` is `EventTrembleEdtConsistent` whenever `u > 0`**
  (`diag_delta1_d2`), so on the Nice Demon both pure labels are tremble-consistent while
  `V(δ₁) = 1 < 2 = V(δ₂)` (`niceDemon_d2_both`, `niceDemon_values`) — tremble-consistent but
  suboptimal, on a literature tree. **When `u < 0` `δ₁` is not** (`diag_delta1_not_d2`): on
  the Mean Demon the sampler makes trembling to `2` look better (`−50ε > −50(1 − ε/2)`), so
  under Definition 6 neither pure label is tremble-consistent and the only candidate is the
  `2/3` tie (`meanDemon_not_d2`).
* **6′** (the shared seed): the sample equals the live draw, `e'(1) = u`, `e'(2) = v` at every
  label (`diag_e'_a/_b`), `V'(q) = uq + v(1−q)` (`diag_value'`); no interior tie unless `u = v`
  (`diag_tie'_iff`); the Jeffrey values of the Mean Demon are `(−50, −100)` at every `x`
  (`meanDemon_e'`), so the evidential evaluator selects `δ₁` under 6′ and the Savage tie of the
  marginal-fixed cf `(ux, v(1−x))` (`c`-data) is at `x = v/(u+v) = 2/3` (`diagSavageCf_tie_iff`).
* **Skyrms's `.9/.1` prior** is the 6′ law at `q₁ = 9/10` (diagonal mass `(9/10, 1/10)`), while
  the Definition-6 law there has off-diagonal mass `18/100` (`diag_law_nine_tenths`); `V' = 11/10`
  on the Nice Demon there (`niceDemon_value'_nine_tenths`).
* The miniature under 6′ pays `0` on every run (`miniature_value'_zero`): every label is a
  fixed point of every evaluator — the phenomenon of Remark 4.3 is the sampler's, not the
  demon's (findings F-N).

Fidelity: Definition 6 rows exact; 6′ rows `variant: 6′`; the Savage cf is `c`-data.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Diagonal payoff: `u` on `(1,1)`, `v` on `(2,2)`, `0` off the diagonal.
Source: Skyrms, *Ratifiability and the logic of decision* (Nice Demon `:236–249`: `1`, `2`; Mean
Demon `:399–412`: `−50`, `−100`); L3-11′
Kind: D -/
def diagPay (u v : ℚ) (s l : Act2) : ℚ :=
  if s = l then (if s = .a then u else v) else 0

/-- **The demon tree**: the demon's sample (a hypothetical query of `d`) then the live query —
Remark 4.3's miniature with diagonal payoffs.
Source: L3-11′ ("encoded as a hypothetical query of `d` (the demon's sample) followed by the live
query"); mandate T10(a)(b)
Kind: D -/
def diagDemon (u v : ℚ) : Tree MiniW Unit (fun _ => Act2) ℚ :=
  .decision () fun s => .decision () fun l => .leaf (s, l) (diagPay u v s l)

/-- `|Act2| = 2` in `ℚ`. Source: none: infrastructure. Kind: L -/
theorem act2_card : (Fintype.card Act2 : ℚ) = 2 := by
  rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num

/-- The Nice Demon `(1, 2)`. Source: Skyrms Ratif. `:236–249`; L3-11′. Kind: D -/
def niceDemon : Tree MiniW Unit (fun _ => Act2) ℚ := diagDemon 1 2

/-- The Mean Demon `(−50, −100)`. Source: Skyrms Ratif. `:399–412`; dp-sl-039. Kind: D -/
def meanDemon : Tree MiniW Unit (fun _ => Act2) ℚ := diagDemon (-50) (-100)

section diag

variable (u v : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the four leaves. Source: none: infrastructure. Kind: L -/
theorem diagDemon_sum {M : Type} [AddCommMonoid M] (f : (diagDemon u v).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ l : Act2, f ⟨s, l, ()⟩ := by
  unfold diagDemon at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `()` is queried. Source: none: infrastructure. Kind: L -/
theorem diagDemon_queried : () ∈ queried (diagDemon u v) := by
  unfold diagDemon; simp [queried_decision]

/-- `nuPoly ⊤ ≠ 0`. Source: none: infrastructure. Kind: L -/
theorem diagDemon_nuPoly_obs_ne_zero : nuPoly C (diagDemon u v) (miniObs ()) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.a, .a, ()⟩, by simp [miniObs], ?_⟩
  unfold diagDemon; simp [chanceWeight]

/-- `ν(live = a) = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem diag_nu_live (a : Act2) : nu C (diagDemon u v) (miniActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, diagDemon_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;> simp [Act2.sum_univ, diagDemon, miniActEv] <;> rw [hb] <;> ring

/-- `𝔼[r · 1_{live = 1}] = u·q²`. Source: none: infrastructure. Kind: L -/
theorem diag_paySum_a : paySum C (diagDemon u v) (miniActEv () .a) = u * (C ()).w .a ^ 2 := by
  rw [paySum_eq_sum_ite, diagDemon_sum]
  simp [Act2.sum_univ, diagDemon, miniActEv, diagPay]
  ring

/-- `𝔼[r · 1_{live = 2}] = v·(1−q)²`. Source: none: infrastructure. Kind: L -/
theorem diag_paySum_b : paySum C (diagDemon u v) (miniActEv () .b) = v * (C ()).w .b ^ 2 := by
  rw [paySum_eq_sum_ite, diagDemon_sum]
  simp [Act2.sum_univ, diagDemon, miniActEv, diagPay]
  ring

/-- The strictly calibrated act value `e(a) = 𝔼[r ∣ live = a]`. Source: L3-11′. Kind: D -/
noncomputable def diagE (a : Act2) : ℚ := condExp C (diagDemon u v) (miniActEv () a ∩ miniObs ())

/-- **`e(1) = u·q`** at `0 < q` (the sampler). Source: L3-11′ ("strict evidential `{1: 1}`" at
`δ₁`); mandate T10. Kind: P. Fidelity: exact. Hyps: (a) `0 < q` -/
theorem diag_e_a (hq : 0 < (C ()).w .a) : diagE u v C .a = u * (C ()).w .a := by
  unfold diagE condExp
  rw [miniObs, Finset.inter_univ, diag_paySum_a, diag_nu_live]
  field_simp

/-- **`e(2) = v·(1−q)`** at `0 < 1 − q`. Source: L3-11′; mandate T10. Kind: P. Fidelity: exact.
Hyps: (a) `0 < 1 − q` -/
theorem diag_e_b (hq : 0 < (C ()).w .b) : diagE u v C .b = v * (C ()).w .b := by
  unfold diagE condExp
  rw [miniObs, Finset.inter_univ, diag_paySum_b, diag_nu_live]
  field_simp

/-- **`V_B(q) = u·q² + v·(1−q)²`** (Nice Demon: `3q² − 4q + 2`).
Source: L3-11′ ("`V_B(q) = 3q² − 4q + 2`"); mandate T10(b)
Kind: P
Fidelity: exact -/
theorem diag_value : value C (diagDemon u v) = u * (C ()).w .a ^ 2 + v * (C ()).w .b ^ 2 := by
  unfold value
  rw [diagDemon_sum]
  simp [Act2.sum_univ, diagDemon, diagPay]
  ring

/-- **The Definition-6 tie**: at a properly mixed label `e(1) = e(2)` iff `q = v/(u+v)` (when
`u + v ≠ 0`) — `2/3` for both demons: the sampler's tie, the miniature's phenomenon.
Source: dp-sl-039 ("under Definition 6 the sampler makes the strict values tie at `2/3` for
both evaluators"); mandate T10(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q < 1`, `u + v ≠ 0` -/
theorem diag_tie_iff (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (huv : u + v ≠ 0) :
    diagE u v C .a = diagE u v C .b ↔ (C ()).w .a = v / (u + v) := by
  rw [diag_e_a u v C hqa, diag_e_b u v C hqb]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  rw [hb]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- The trembled values of `δ₁`: under `C^ε` with `C = δ₁`, `e(1) = u(1 − ε/2)`, `e(2) = v·ε/2`.
Source: L3-11′ ("trembled `{1: 1 − ε/2, 2: ε}`" on the Nice Demon); mandate T10(b)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ 1` -/
theorem diag_tremble_e (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    diagE u v (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1) .a = u * (1 - ε / 2) ∧
      diagE u v (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1) .b = v * (ε / 2) := by
  have hwa : (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1 ()).w .a = 1 - ε / 2 := by
    simp [tremble_w, Proc.ofFun, act2_card]; ring
  have hwb : (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1 ()).w .b = ε / 2 := by
    simp [tremble_w, Proc.ofFun, act2_card]; ring
  constructor
  · rw [diag_e_a u v _ (by rw [hwa]; linarith), hwa]
  · rw [diag_e_b u v _ (by rw [hwb]; linarith), hwb]

/-- **T10(b): `δ₁` is event-tremble-EDT-consistent whenever `u > 0`** (Definition 6, D2): for
`ε < 2u/(u + max v 0)`-small trembles the supported act `1` has `u(1 − ε/2) ≥ v·ε/2`.
Source: dp-sl-2-053 ("the suboptimal deterministic procedure `δ₁` is fixed-form
tremble-EDT-consistent"); L3-11′; mandate T10(b)
Kind: P
Fidelity: exact (`dp-calibration`'s `EventTrembleEdtConsistent`, on the demon tree)
Hyps: (a) `0 < u` -/
theorem diag_delta1_d2 (hu : 0 < u) :
    EventTrembleEdtConsistent miniObs miniActEv (Proc.ofFun fun _ => Act2.a) (diagDemon u v) := by
  -- the threshold: `ε ≤ ε₀ := u / (u + |v|)` gives `v ε/2 ≤ u(1 − ε/2)`
  refine ⟨u / (u + |v|), by positivity, ?_⟩
  intro ε h0 h1 hε d _ _ _ a ha
  cases d
  have ha' : a = .a := by
    cases a
    · rfl
    · simp [Proc.ofFun] at ha
  subst ha'
  obtain ⟨hea, heb⟩ := diag_tremble_e u v ε h0 h1
  have hwa : (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1 ()).w .a = 1 - ε / 2 := by
    simp [tremble_w, Proc.ofFun, act2_card]; ring
  have hle : ε * (u + |v|) < u := (lt_div_iff₀ (by positivity : (0 : ℚ) < u + |v|)).mp hε
  have hvle : v ≤ |v| := le_abs_self v
  refine ⟨?_, ?_⟩
  · rw [miniObs, Finset.inter_univ, diag_nu_live, hwa]; linarith
  · intro b _
    change diagE u v _ b ≤ diagE u v _ .a
    cases b
    · exact le_rfl
    · rw [hea, heb]
      have h1 : ε * v ≤ ε * |v| := mul_le_mul_of_nonneg_left hvle h0.le
      nlinarith [hle, h1, hu, h0]

/-- **`δ₁` is not event-tremble-EDT-consistent when `u < 0`**: for every `ε₀` some smaller `ε`
has `v·ε/2 > u(1 − ε/2)` (the Mean Demon: `−50ε > −50(1 − ε/2)` for `ε < 2/3`).
Source: dp-sl-039 (the Mean Demon under Definition 6: both evaluators tie at `2/3`, no pure label
is approved); mandate T10(a)
Kind: P
Fidelity: exact
Hyps: (a) `u < 0` -/
theorem diag_delta1_not_d2 (hu : u < 0) :
    ¬ EventTrembleEdtConsistent miniObs miniActEv (Proc.ofFun fun _ => Act2.a) (diagDemon u v) := by
  rintro ⟨ε₀, hε₀, h⟩
  -- a tremble below `ε₀`, below `1` and below `−u/(1 + |u| + |v|)`
  obtain ⟨ε, hpos, hle1, hlt0, hsmall⟩ : ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ ε < ε₀ ∧
      ε * (1 + |u| + |v|) ≤ -u := by
    refine ⟨min (ε₀ / 2) (min 1 (-u / (1 + |u| + |v|))), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (lt_min one_pos (div_pos (by linarith) (by positivity)))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have : min (ε₀ / 2) (min 1 (-u / (1 + |u| + |v|))) ≤ -u / (1 + |u| + |v|) :=
        le_trans (min_le_right (ε₀ / 2) _) (min_le_right 1 _)
      rwa [le_div_iff₀ (by positivity : (0 : ℚ) < 1 + |u| + |v|)] at this
  have hex : ∃ b, 0 < nu (tremble (Proc.ofFun fun _ => Act2.a) ε hpos.le hle1) (diagDemon u v)
      (miniActEv () b ∩ miniObs ()) := by
    refine ⟨.a, ?_⟩
    rw [miniObs, Finset.inter_univ, diag_nu_live]
    simp [tremble_w, Proc.ofFun, act2_card]; linarith
  have h1 := (h ε hpos hle1 hlt0 () (diagDemon_queried u v) (diagDemon_nuPoly_obs_ne_zero u v _)
    hex .a (by simp [Proc.ofFun])).2 .b (by
      rw [miniObs, Finset.inter_univ, diag_nu_live]
      simp [tremble_w, Proc.ofFun, act2_card]; linarith)
  change diagE u v _ .b ≤ diagE u v _ .a at h1
  obtain ⟨hea, heb⟩ := diag_tremble_e u v ε hpos hle1
  rw [hea, heb] at h1
  -- `ε v ≤ 2u − ε u`, while `ε u + ε v ≥ −ε|u| − ε|v| ≥ u + ε`: so `ε ≤ u < 0`
  have hεu : ε * (-|u|) ≤ ε * u := mul_le_mul_of_nonneg_left (neg_abs_le u) hpos.le
  have hεv : ε * (-|v|) ≤ ε * v := mul_le_mul_of_nonneg_left (neg_abs_le v) hpos.le
  nlinarith [hεu, hεv, hsmall, h1, hu, hpos]

/-! ### The two demons -/

/-- **Nice Demon values**: `V(δ₁) = 1 < 2 = V(δ₂)`, `V_B(q) = 3q² − 4q + 2`.
Source: L3-11′; dp-sl-2-053; mandate T10(b)
Kind: P
Fidelity: exact -/
theorem niceDemon_values :
    value (Proc.ofFun fun _ => Act2.a) niceDemon = 1 ∧ value (Proc.ofFun fun _ => Act2.b) niceDemon = 2 ∧
      value C niceDemon = 3 * (C ()).w .a ^ 2 - 4 * (C ()).w .a + 2 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  unfold niceDemon
  refine ⟨?_, ?_, ?_⟩
  · rw [diag_value]; simp [Proc.ofFun]
  · rw [diag_value]; simp [Proc.ofFun]
  · rw [diag_value, hb]; ring

/-- **T10(b) on the Nice Demon: both pure labels are tremble-consistent, `δ₁` suboptimal** —
"tremble-consistent but suboptimal" on a literature tree (the plan's N+).
Source: dp-sl-2-053; L3-11′ ("Both pure labels are fixed-form tremble-EDT-consistent — including
the suboptimal `δ₁`"); mandate T10(b)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem niceDemon_d2_both :
    EventTrembleEdtConsistent miniObs miniActEv (Proc.ofFun fun _ => Act2.a) niceDemon ∧
      EventTrembleEdtConsistent miniObs miniActEv (Proc.ofFun fun _ => Act2.b) niceDemon ∧
      value (Proc.ofFun fun _ => Act2.a) niceDemon < value (Proc.ofFun fun _ => Act2.b) niceDemon := by
  refine ⟨diag_delta1_d2 1 2 one_pos, ?_, ?_⟩
  · -- `δ₂` by the symmetry `(u, v, 1, 2) ↦ (v, u, 2, 1)`: proved directly
    refine ⟨2 / (2 + 1), by norm_num, ?_⟩
    intro ε h0 h1 hε d _ _ _ a ha
    cases d
    have ha' : a = .b := by
      cases a
      · simp [Proc.ofFun] at ha
      · rfl
    subst ha'
    have hwa : (tremble (Proc.ofFun fun _ => Act2.b) ε h0.le h1 ()).w .a = ε / 2 := by
      simp [tremble_w, Proc.ofFun, act2_card]; ring
    have hwb : (tremble (Proc.ofFun fun _ => Act2.b) ε h0.le h1 ()).w .b = 1 - ε / 2 := by
      simp [tremble_w, Proc.ofFun, act2_card]; ring
    refine ⟨?_, ?_⟩
    · rw [miniObs, Finset.inter_univ]; unfold niceDemon; rw [diag_nu_live, hwb]; linarith
    · intro b _
      unfold niceDemon
      change diagE 1 2 _ b ≤ diagE 1 2 _ .b
      cases b
      · rw [diag_e_a 1 2 _ (by rw [hwa]; linarith), diag_e_b 1 2 _ (by rw [hwb]; linarith), hwa, hwb]
        linarith
      · exact le_rfl
  · obtain ⟨h1, h2, -⟩ := niceDemon_values (Proc.ofFun fun _ => Act2.a)
    rw [h1, h2]; norm_num

/-- **The Mean Demon under Definition 6: `δ₁` is not tremble-consistent**, and the mixed tie is
at `2/3` (`diag_tie_iff` at `(−50, −100)`).
Source: dp-sl-039; mandate T10(a)
Kind: P
Fidelity: exact -/
theorem meanDemon_not_d2 :
    ¬ EventTrembleEdtConsistent miniObs miniActEv (Proc.ofFun fun _ => Act2.a) meanDemon ∧
      ∀ C : Proc Unit (fun _ => Act2) ℚ, 0 < (C ()).w .a → 0 < (C ()).w .b →
        (diagE (-50) (-100) C .a = diagE (-50) (-100) C .b ↔ (C ()).w .a = 2 / 3) := by
  refine ⟨diag_delta1_not_d2 (-50) (-100) (by norm_num), fun C hqa hqb => ?_⟩
  rw [diag_tie_iff (-50) (-100) C hqa hqb (by norm_num)]; norm_num

/-! ### The shared seed -/

/-- The 6′ law on the demon tree: `μ'(s, l) = C(d)(s)·[s = l]`. Source: `seeds.md` Definition 6′;
L3-11′ ("the sample equals the live draw"). Kind: P. Fidelity: exact -/
theorem diag_leafLaw' (s l : Act2) :
    leafLaw' C (diagDemon u v) ⟨s, l, ()⟩ = (C ()).w s * (if s = l then 1 else 0) := by
  unfold leafLaw' diagDemon
  rw [leafLawSeed_decision_of_none C rfl, leafLawSeed_decision_of_some C (a' := s) (by simp)]
  simp only [leafLawSeed_leaf]

/-- `ν'(live = a) = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem diag_nu'_live (a : Act2) : nu' C (diagDemon u v) (miniActEv () a) = (C ()).w a := by
  rw [nu'_eq_sum_ite, diagDemon_sum]
  simp only [diag_leafLaw']
  cases a <;> simp [Act2.sum_univ, diagDemon, miniActEv]

/-- `𝔼'[r · 1_{live = 1}] = u·q`, `𝔼'[r · 1_{live = 2}] = v·(1−q)`. Source: none: infrastructure.
Kind: L -/
theorem diag_paySumSeed :
    paySumSeed C (diagDemon u v) (miniActEv () .a) = u * (C ()).w .a ∧
      paySumSeed C (diagDemon u v) (miniActEv () .b) = v * (C ()).w .b := by
  constructor <;>
  · rw [paySumSeed_eq_sum_ite, diagDemon_sum]
    simp only [diag_leafLaw']
    simp [Act2.sum_univ, diagDemon, miniActEv, diagPay, mul_comm]

/-- The 6′ conditional act value. Source: L3-11′ ("Jeffrey"). Kind: D. Fidelity: variant: 6′ -/
noncomputable def diagE' (a : Act2) : ℚ :=
  condExpSeed C (diagDemon u v) (miniActEv () a ∩ miniObs ())

/-- **Under 6′ `e'(1) = u` at every label with `0 < q`** (Skyrms's `pr(State i ∣ Act i) = 1`).
Source: L3-11′ ("the trembled and limit evidential values are `{1: 1, 2: 2}` at both pure
labels"); dp-sl-039 ("Jeffrey values `(−50, −100)` at every `x`"); mandate T10(a)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < q` -/
theorem diag_e'_a (hq : 0 < (C ()).w .a) : diagE' u v C .a = u := by
  unfold diagE' condExpSeed
  rw [miniObs, Finset.inter_univ, (diag_paySumSeed u v C).1, diag_nu'_live]
  field_simp

/-- **Under 6′ `e'(2) = v`** at `0 < 1 − q`. Source: as `diag_e'_a`. Kind: P. Fidelity: variant: 6′.
Hyps: (a) `0 < 1 − q` -/
theorem diag_e'_b (hq : 0 < (C ()).w .b) : diagE' u v C .b = v := by
  unfold diagE' condExpSeed
  rw [miniObs, Finset.inter_univ, (diag_paySumSeed u v C).2, diag_nu'_live]
  field_simp

/-- **`V'(q) = u·q + v·(1−q)`** under 6′ (Nice Demon: `2 − q`). Source: L3-11′ ("`V_B(q) = 2 − q`").
Kind: P. Fidelity: variant: 6′ -/
theorem diag_value' : value' C (diagDemon u v) = u * (C ()).w .a + v * (C ()).w .b := by
  unfold value'
  rw [diagDemon_sum]
  simp only [diag_leafLaw']
  simp [Act2.sum_univ, diagDemon, diagPay, mul_comm]

/-- **No interior tie under 6′ unless `u = v`**: at a properly mixed label `e'(1) = e'(2)` iff
`u = v` — the Mean Demon has none (`−50 ≠ −100`): the evidential evaluator selects `δ₁`.
Source: dp-sl-039 ("no interior tie; the total evidential evaluator selects `δ₁`"); mandate T10(a)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < q < 1` -/
theorem diag_tie'_iff (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    diagE' u v C .a = diagE' u v C .b ↔ u = v := by
  rw [diag_e'_a u v C hqa, diag_e'_b u v C hqb]

/-- The Mean Demon's Jeffrey values under 6′ are `(−50, −100)` at every properly mixed label.
Source: dp-sl-039; mandate T10(a). Kind: N+. Fidelity: variant: 6′ -/
theorem meanDemon_e' (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    diagE' (-50) (-100) C .a = -50 ∧ diagE' (-50) (-100) C .b = -100 :=
  ⟨diag_e'_a _ _ C hqa, diag_e'_b _ _ C hqb⟩

/-- **The marginal-fixed (Savage) cf** `(u·x, v·(1−x))` — `c`-data: supposes the demon's marginal
`x` fixed while the act varies.
Source: dp-sl-039 ("the Savage tie of the `K`-marginal-fixed cf (`c`-data: `c₁(x) = −50x`,
`c₂(x) = −100(1−x)`) is at `x = 2/3`"); mandate T10(a)
Kind: D
Fidelity: variant: cf reduced to act values; `Hyps: (c)` -/
def diagSavageCf (x : ℚ) : Act2 → ℚ
  | .a => u * x
  | .b => v * (1 - x)

/-- The Savage cf ties iff `x = v/(u+v)` (`2/3` for both demons). Source: dp-sl-039. Kind: L.
Hyps: (c) the cf's values; (a) `u + v ≠ 0` -/
theorem diagSavageCf_tie_iff (huv : u + v ≠ 0) (x : ℚ) :
    diagSavageCf u v x .a = diagSavageCf u v x .b ↔ x = v / (u + v) := by
  simp only [diagSavageCf]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **Skyrms's `.9/.1` prior is the 6′ law at `q₁ = 9/10`**: diagonal mass `(9/10, 1/10)` and no
off-diagonal mass; the Definition-6 law at the same label has off-diagonal mass `18/100`.
Source: L3-11′ ("Skyrms's '.9/.1 on the diagonal' prior is the shared-seed law at `q₁ = 9/10`
(the independent law there has off-diagonal mass `18/100`)"); mandate T10(b)
Kind: L
Fidelity: exact -/
theorem diag_law_nine_tenths :
    leafLaw' (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.a, .a, ()⟩ = 9 / 10 ∧
    leafLaw' (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.b, .b, ()⟩ = 1 / 10 ∧
    leafLaw' (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.a, .b, ()⟩ = 0 ∧
    leafLaw' (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.b, .a, ()⟩ = 0 ∧
    leafLaw (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.a, .b, ()⟩ +
      leafLaw (procQ (9/10) (by norm_num) (by norm_num)) (diagDemon u v) ⟨.b, .a, ()⟩ = 18 / 100 := by
  simp only [diag_leafLaw']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [procQ]
  · simp [procQ]; norm_num
  · simp
  · simp
  · simp [diagDemon, procQ]; norm_num

/-- `V' = 11/10` on the Nice Demon at Skyrms's prior. Source: L3-11′ ("`V_B = 11/10`"). Kind: N+.
Fidelity: variant: 6′ -/
theorem niceDemon_value'_nine_tenths :
    value' (procQ (9/10) (by norm_num) (by norm_num)) niceDemon = 11 / 10 := by
  unfold niceDemon; rw [diag_value']; simp [procQ]; norm_num

/-- **The miniature under 6′ pays `0` on every run** (its payoffs are off-diagonal, the seed keeps
the run on the diagonal): `V' ≡ 0`, so every label is a fixed point of every 6′ evaluator — the
mixed fixed point of Remark 4.3 is the sampler's phenomenon, not the demon's (findings F-N).
Source: dp-sl-039 ("the miniature under 6′ has `r ≡ 0` with every `q` a fixed point"); mandate
T10(a)
Kind: P
Fidelity: variant: 6′ -/
theorem miniature_value'_zero : value' C miniature = 0 := by
  unfold value'
  rw [miniature_sum]
  have h : ∀ s l : Act2, leafLaw' C miniature ⟨s, l, ()⟩ = (C ()).w s * (if s = l then 1 else 0) := by
    intro s l
    unfold leafLaw' miniature
    rw [leafLawSeed_decision_of_none C rfl, leafLawSeed_decision_of_some C (a' := s) (by simp)]
    simp only [leafLawSeed_leaf]
  simp only [h]
  simp [Act2.sum_univ, miniature, miniPay]

end diag

end Cleanroom.Decision.DpDutchBook
