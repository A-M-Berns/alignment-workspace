import Cleanroom.Decision.DpDutchBook.Newcomb

/-!
# T6: draw-keyed Death in Damascus with `(p, L, c)` free

`didRouted p L c` (dp-sl-034's tree, "routing on the act = draw-keyed"): the live query first
(`.a` = stay, `.b` = flee); then a chance node with skill `p`: on index `0` Death is at the
agent's city, on index `1` Death's city is a fresh draw from the label (a simulation `d`-node).
Payoff `L` on survival (`loc ≠ act`; equivalently loss `L` on being found, up to the constant),
`−c` for fleeing. Everything below is computed from the tree under Definition 6, with `q :=
C(d)(stay)`:

* `e(stay) = L(1−p)(1−q)`, `e(flee) = L(1−p)q − c`, so **`e(stay) − e(flee) = L(1−p)(1−2q) + c`**
  (`did_e_sub`; dp-sl-034's `1000(1−p)(1−2q) + 1` is the `(1000, 1)` instance);
* **Death's marginal is `q` for every `p`** (`did_death_marginal`);
* the **unique interior tie** `q*(p) = ½ + c/(2L(1−p))`, in `(0,1)` iff `p < 1 − c/L`
  (`did_tie_iff`, `did_tie_interior_iff`); for `p ≥ 1 − c/L` stay weakly dominates at every label
  (`did_stay_dominates`, the general form of `stay_dominates_high_skill`'s box inequality);
* **the prior value** `V_B(q) = −2L(1−p)q² + (2L(1−p) + c)q − c` (`did_value`), with the
  completed square `V_B(q) = V_B(q_opt) − 2L(1−p)(q − q_opt)²` at `q_opt = ½ + c/(4L(1−p))`
  (`did_value_sq`), hence `V_B ≤ V_B(q_opt)` (`did_value_le_opt`), `q_opt ≤ 1` iff
  `p ≤ 1 − c/(2L)` (`did_qopt_le_one_iff`), and **`V_B(q_opt) − V_B(q*) = c²/(8L(1−p))`**
  with `V_B(q*) = V_B(½)` (`did_gap`): ratifiable ≠ optimal;
* **the band** `1 − c/L ≤ p ≤ 1 − c/(2L)` (dp-sl-2-009(iv), UNREVIEWED in the source): the
  optimum is interior while no interior tie exists and stay strictly dominates at every properly
  mixed label (`did_band`) — proved;
* the marginal-holding cf `(L(1−q), Lq − c)` (`c`-data) ties at `½ + c/(2L)` for every `p`
  (`didClassicalCf_tie_iff`), and at `p = 1` agrees with conditioning at no label with `q < 1`
  (`didClassicalCf_ne_e_perfect`).

**Finding (dp-sl-2-009(i)/(iii))**: the source labels `−2000q² + 2001q − 1` as the `p = ½`
instance at `(1000, 1)`; it is the `p = 0` instance (`−2L(1−p) = −2000` forces `p = 0`;
dp-sl-034 says so), and its `1/8000` is `c²/(8L(1−p))` at `p = 0`. At `p = ½` the gap is
`c²/(4L) = 1/4000` (`did_gap_inst`). See findings F-M.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Death-in-Damascus worlds `(act, Death's city)`; `.a` = stay (Damascus), `.b` = flee (Aleppo).
Source: dp-sl-034; `repair/P03.md` Import 2
Kind: D -/
abbrev DidW : Type := Act2 × Act2

/-- Payoff: `L` on survival (`loc ≠ act`), `−c` for fleeing.
Source: dp-sl-034 (`evStay = L(1−p)(1−q)`: survival pays `L`); mandate T6
Kind: D
Fidelity: variant: `L` on survival rather than `−L` on being found (a constant shift) -/
def didPay (L c : ℚ) : DidW → ℚ
  | (act, loc) => (if loc = act then 0 else L) - (if act = .b then c else 0)

/-- The chance children after the live act `act`: index `0` (skill) — Death at `act`'s city;
index `1` — Death's city a fresh draw from the label.
Source: dp-sl-034 ("Death's location a post-decision chance node keyed to the live draw with
skill `p`")
Kind: D -/
def didChild (L c : ℚ) (act : Act2) : Fin 2 → Tree DidW Unit (fun _ => Act2) ℚ
  | ⟨0, _⟩ => .leaf (act, act) (didPay L c (act, act))
  | ⟨_ + 1, _⟩ => .decision () fun loc => .leaf (act, loc) (didPay L c (act, loc))

/-- **Draw-keyed Death in Damascus** `didRouted p L c`: live query, then the skill coin.
Source: dp-sl-034; dp-sl-2-009; mandate T6 (`didRouted p L c`)
Kind: D -/
def didRouted (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L c : ℚ) : Tree DidW Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .chance 2 (FinDistr.coin p h0 h1) (didChild L c act)

/-- Action events: the act coordinate. Source: v2 §2 Definition 3. Kind: D -/
def didActEv : (d : Unit) → Act2 → Finset DidW
  | _, act => Finset.univ.filter fun w => w.1 = act

/-- Death's-city events. Source: none: infrastructure. Kind: D -/
def didDeathEv (loc : Act2) : Finset DidW := Finset.univ.filter fun w => w.2 = loc

/-- The observation `⊤` (the agent sees nothing before acting). Source: mandate T6. Kind: D -/
def didObs : Unit → Finset DidW := fun _ => Finset.univ

section tree

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L c : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- The skill child is the leaf. Source: none: infrastructure. Kind: L -/
theorem didChild_zero (act : Act2) :
    didChild L c act 0 = .leaf (act, act) (didPay L c (act, act)) := rfl

/-- The simulation child. Source: none: infrastructure. Kind: L -/
theorem didChild_one (act : Act2) :
    didChild L c act 1 = .decision () fun loc => .leaf (act, loc) (didPay L c (act, loc)) := rfl

/-- Sums over the six leaves. Source: none: infrastructure. Kind: L -/
theorem didRouted_sum (f : (didRouted p h0 h1 L c).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ act : Act2, (f ⟨act, 0, ()⟩ + ∑ loc : Act2, f ⟨act, 1, loc, ()⟩) := by
  unfold didRouted at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have e0 : ∑ ℓ : (didChild L c act 0).Leaves, f ⟨act, 0, ℓ⟩ = f ⟨act, 0, ()⟩ := by
    show ∑ ℓ : Unit, f ⟨act, 0, ℓ⟩ = f ⟨act, 0, ()⟩
    simp
  have e1 : ∑ ℓ : (didChild L c act 1).Leaves, f ⟨act, 1, ℓ⟩ = ∑ loc : Act2, f ⟨act, 1, loc, ()⟩ := by
    show ∑ ℓ : (Tree.decision () (fun loc : Act2 => Tree.leaf (act, loc) (didPay L c (act, loc))) :
        Tree DidW Unit (fun _ => Act2) ℚ).Leaves, f ⟨act, 1, ℓ⟩ = _
    rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun loc _ => ?_
    show ∑ ℓ : Unit, f ⟨act, 1, loc, ℓ⟩ = f ⟨act, 1, loc, ()⟩
    simp
  rw [e0, e1]

/-- `ν(act = a) = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem did_nu_act (a : Act2) : nu C (didRouted p h0 h1 L c) (didActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, didRouted_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didActEv, FinDistr.coin] <;>
    rw [hb] <;> ring

/-- `𝔼[r · 1_{stay}] = q · L(1−p)(1−q)`. Source: none: infrastructure. Kind: L -/
theorem did_paySum_stay :
    paySum C (didRouted p h0 h1 L c) (didActEv () .a) =
      (C ()).w .a * (L * (1 - p) * (C ()).w .b) := by
  rw [paySum_eq_sum_ite, didRouted_sum]
  simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didActEv, didPay, FinDistr.coin]
  ring

/-- `𝔼[r · 1_{flee}] = (1−q) · (L(1−p)q − c)`. Source: none: infrastructure. Kind: L -/
theorem did_paySum_flee :
    paySum C (didRouted p h0 h1 L c) (didActEv () .b) =
      (C ()).w .b * (L * (1 - p) * (C ()).w .a - c) := by
  rw [paySum_eq_sum_ite, didRouted_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didActEv, didPay, FinDistr.coin]
  rw [hb]; ring

/-- The strictly calibrated act value `e(a) = 𝔼[r ∣ a]` (`O_d = ⊤`).
Source: dp-sl-034 (`V_s(stay)`, `V_s(flee)`); mandate T6
Kind: D -/
noncomputable def didE (a : Act2) : ℚ :=
  condExp C (didRouted p h0 h1 L c) (didActEv () a ∩ didObs ())

/-- **`e(stay) = L(1−p)(1−q)`** at `0 < q`. Source: dp-sl-034 (`evStay`); mandate T6.
Kind: P. Fidelity: exact. Hyps: (a) `0 < q` -/
theorem didE_stay (hq : 0 < (C ()).w .a) : didE p h0 h1 L c C .a = L * (1 - p) * (C ()).w .b := by
  unfold didE condExp
  rw [didObs, Finset.inter_univ, did_paySum_stay, did_nu_act]
  field_simp

/-- **`e(flee) = L(1−p)q − c`** at `0 < 1 − q`. Source: dp-sl-034 (`evFlee`); mandate T6.
Kind: P. Fidelity: exact. Hyps: (a) `0 < 1 − q` -/
theorem didE_flee (hq : 0 < (C ()).w .b) :
    didE p h0 h1 L c C .b = L * (1 - p) * (C ()).w .a - c := by
  unfold didE condExp
  rw [didObs, Finset.inter_univ, did_paySum_flee, did_nu_act]
  field_simp

/-- **`e(stay) − e(flee) = L(1−p)(1−2q) + c`** at a properly mixed label (dp-sl-034's
`1000(1−p)(1−2q) + 1` at `(1000, 1)`).
Source: dp-sl-034 (`ev_diff`); mandate T6
Kind: P
Fidelity: exact (general `(L, c)`)
Hyps: (a) `0 < q < 1` -/
theorem did_e_sub (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    didE p h0 h1 L c C .a - didE p h0 h1 L c C .b = L * (1 - p) * (1 - 2 * (C ()).w .a) + c := by
  rw [didE_stay p h0 h1 L c C hqa, didE_flee p h0 h1 L c C hqb]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  rw [hb]; ring

/-- **Death's marginal is the label, for every skill**: `ν(loc = a) = C(d)(a)`.
Source: dp-sl-034 ("Death's marginal `= q` for every `p`"; `classical_marginal`); mandate T6
Kind: P
Fidelity: exact -/
theorem did_death_marginal (a : Act2) :
    nu C (didRouted p h0 h1 L c) (didDeathEv a) = (C ()).w a := by
  rw [nu_eq_sum, didRouted_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didDeathEv, FinDistr.coin] <;>
    rw [hb] <;> ring

/-! ### The tie and dominance -/

/-- **The tie equation**: at a properly mixed label, `e(stay) = e(flee)` iff
`q = ½ + c/(2L(1−p))` (for `p < 1`, `L > 0`).
Source: dp-sl-034 (`ev_tie`); mandate T6
Kind: P
Fidelity: exact
Hyps: (a) `0 < q < 1`, `p < 1`, `0 < L` -/
theorem did_tie_iff (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hp : p < 1) (hL : 0 < L) :
    didE p h0 h1 L c C .a = didE p h0 h1 L c C .b ↔
      (C ()).w .a = 1 / 2 + c / (2 * L * (1 - p)) := by
  have h := did_e_sub p h0 h1 L c C hqa hqb
  have hpos : 0 < L * (1 - p) := mul_pos hL (by linarith)
  have h1p : (1 - p) ≠ 0 := (sub_pos.mpr hp).ne'
  have hid : 1 / 2 + c / (2 * L * (1 - p)) - (C ()).w .a =
      (L * (1 - p) * (1 - 2 * (C ()).w .a) + c) / (2 * L * (1 - p)) := by
    field_simp; ring
  constructor
  · intro heq
    have key : L * (1 - p) * (1 - 2 * (C ()).w .a) + c = 0 := by linarith
    rw [key, zero_div] at hid
    linarith
  · intro hq
    have : (L * (1 - p) * (1 - 2 * (C ()).w .a) + c) / (2 * L * (1 - p)) = 0 := by
      rw [← hid, hq]; ring
    rw [div_eq_zero_iff] at this
    rcases this with h' | h'
    · linarith
    · exfalso; exact (by positivity : (2 * L * (1 - p)) ≠ 0) h'

/-- **The tie is interior iff `p < 1 − c/L`**: `0 < ½ + c/(2L(1−p)) < 1` iff `c < L(1−p)`
(for `p < 1`, `L > 0`, `c > 0`).
Source: dp-sl-034 ("unique interior tie … iff `p < 1 − c/L`"); dp-sl-2-009(ii); mandate T6
Kind: P
Fidelity: exact
Hyps: (a) `p < 1`, `0 < L`, `0 < c` -/
theorem did_tie_interior_iff (hp : p < 1) (hL : 0 < L) (hc : 0 < c) :
    (0 < 1 / 2 + c / (2 * L * (1 - p)) ∧ 1 / 2 + c / (2 * L * (1 - p)) < 1) ↔ p < 1 - c / L := by
  have hpos : 0 < 2 * L * (1 - p) := by nlinarith
  constructor
  · rintro ⟨-, hlt⟩
    have : c / (2 * L * (1 - p)) < 1 / 2 := by linarith
    rw [div_lt_iff₀ hpos] at this
    have : c / L < 1 - p := by rw [div_lt_iff₀ hL]; linarith
    linarith
  · intro h
    have : c / L < 1 - p := by linarith
    rw [div_lt_iff₀ hL] at this
    refine ⟨by positivity, ?_⟩
    have : c / (2 * L * (1 - p)) < 1 / 2 := by rw [div_lt_iff₀ hpos]; linarith
    linarith

/-- **Stay weakly dominates for `p ≥ 1 − c/L`** at every label (the general form of
`stay_dominates_high_skill`'s box inequality: `L(1−p)(1−2q) + c ≥ 0` for `q ≤ 1`).
Source: dp-sl-034 (`stay_dominates_high_skill`, `p ≥ .999` at `(1000, 1)`); mandate T6
Kind: P
Fidelity: exact (general `(L, c)`)
Hyps: (a) `0 < q < 1`, `1 − c/L ≤ p`, `0 < L`, `p ≤ 1` -/
theorem did_stay_dominates (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hL : 0 < L)
    (hp : 1 - c / L ≤ p) :
    didE p h0 h1 L c C .b ≤ didE p h0 h1 L c C .a := by
  have h := did_e_sub p h0 h1 L c C hqa hqb
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hq1 : (C ()).w .a < 1 := by linarith
  have hcL : L * (1 - p) ≤ c := by
    have : 1 - p ≤ c / L := by linarith
    rwa [le_div_iff₀ hL, mul_comm] at this
  have : 0 ≤ L * (1 - p) := mul_nonneg hL.le (by linarith)
  nlinarith

/-! ### The prior value, its optimum, and the gap -/

/-- **The prior value** `V_B(q) = −2L(1−p)q² + (2L(1−p) + c)q − c`.
Source: dp-sl-2-009(i); dp-sl-034 (`V_B(p=0) = −2000q² + 2001q − 1`); mandate T6
Kind: P
Fidelity: exact (general `(p, L, c)`) -/
theorem did_value :
    value C (didRouted p h0 h1 L c) =
      -2 * L * (1 - p) * (C ()).w .a ^ 2 + (2 * L * (1 - p) + c) * (C ()).w .a - c := by
  unfold value
  rw [didRouted_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didPay, FinDistr.coin]
  rw [hb]; ring

/-- The quadratic `V_B` as a function of the stay probability (the closed form of `did_value`).
Source: dp-sl-2-009(i); mandate T6
Kind: D -/
def didV (q : ℚ) : ℚ := -2 * L * (1 - p) * q ^ 2 + (2 * L * (1 - p) + c) * q - c

/-- The stationary point `q_opt = ½ + c/(4L(1−p))`. Source: dp-sl-2-009(i); mandate T6. Kind: D -/
noncomputable def didQopt : ℚ := 1 / 2 + c / (4 * L * (1 - p))

/-- The interior tie `q* = ½ + c/(2L(1−p))`. Source: dp-sl-034; mandate T6. Kind: D -/
noncomputable def didQstar : ℚ := 1 / 2 + c / (2 * L * (1 - p))

/-- **The completed square**: `V_B(q) = V_B(q_opt) − 2L(1−p)(q − q_opt)²` (for `p ≠ 1`, `L ≠ 0`).
Source: dp-sl-2-009(i) (`value_derivative_zero`); mandate T6
Kind: P
Fidelity: exact (no derivative: the algebraic identity)
Hyps: (a) `p ≠ 1`, `L ≠ 0` -/
theorem did_value_sq (hp : p ≠ 1) (hL : L ≠ 0) (q : ℚ) :
    didV p L c q = didV p L c (didQopt p L c) - 2 * L * (1 - p) * (q - didQopt p L c) ^ 2 := by
  unfold didV didQopt
  have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  field_simp
  ring

/-- **`V_B ≤ V_B(q_opt)`** for every `q` when `p < 1`, `0 < L`.
Source: dp-sl-2-009(i)/(iii) ("the optimum"); mandate T6
Kind: P
Hyps: (a) `p < 1`, `0 < L` -/
theorem did_value_le_opt (hp : p < 1) (hL : 0 < L) (q : ℚ) :
    didV p L c q ≤ didV p L c (didQopt p L c) := by
  rw [did_value_sq p L c hp.ne hL.ne' q]
  have : 0 ≤ 2 * L * (1 - p) * (q - didQopt p L c) ^ 2 := by
    apply mul_nonneg (by nlinarith) (sq_nonneg _)
  linarith

/-- **`q_opt ≤ 1` iff `p ≤ 1 − c/(2L)`** (for `p < 1`, `L > 0`).
Source: dp-sl-2-009(i) ("interior iff `p ≤ 1 − c/(2L)`"; `stationary_at_boundary`); mandate T6
Kind: P
Hyps: (a) `p < 1`, `0 < L` -/
theorem did_qopt_le_one_iff (hp : p < 1) (hL : 0 < L) :
    didQopt p L c ≤ 1 ↔ p ≤ 1 - c / (2 * L) := by
  unfold didQopt
  have hpos : 0 < 4 * L * (1 - p) := by nlinarith
  constructor
  · intro h
    have : c / (4 * L * (1 - p)) ≤ 1 / 2 := by linarith
    rw [div_le_iff₀ hpos] at this
    have : c / (2 * L) ≤ 1 - p := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  · intro h
    have : c / (2 * L) ≤ 1 - p := by linarith
    rw [div_le_iff₀ (by linarith)] at this
    have : c / (4 * L * (1 - p)) ≤ 1 / 2 := by rw [div_le_iff₀ hpos]; linarith
    linarith

/-- **The gap: `V_B(q_opt) − V_B(q*) = c²/(8L(1−p))`, and `V_B(q*) = V_B(½)`** — ratifiable ≠
optimal, as a function of `(p, L, c)`. At `(1000, 1)`: `1/8000` at `p = 0` (the earlier Lean's
numerals), `1/4000` at `p = ½`.
Source: dp-sl-2-009(iii) (`optimum_gap`, `value_at_ratifiable`, `value_at_half`); mandate T6
("derive the general gap (the Lean's `1/8000` is the instance)")
Kind: P
Fidelity: exact (general `(p, L, c)`); corrects dp-sl-2-009's "`1/8000` at `p = ½`" (F-M)
Hyps: (a) `p ≠ 1`, `L ≠ 0` -/
theorem did_gap (hp : p ≠ 1) (hL : L ≠ 0) :
    didV p L c (didQopt p L c) - didV p L c (didQstar p L c) = c ^ 2 / (8 * L * (1 - p)) ∧
      didV p L c (didQstar p L c) = didV p L c (1 / 2) := by
  have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  unfold didV didQopt didQstar
  constructor <;> (field_simp; ring)

/-- **The gap at `(1000, 1)`**: `1/8000` at `p = 0` and `1/4000` at `p = ½` — the source's
numerals are the `p = 0` instance.
Source: dp-sl-2-009(iii) (the quoted "`1/8000` at `p = ½`"); `P03-did-referents.lean:79–91`
Kind: N+
Fidelity: exact -/
theorem did_gap_inst :
    didV 0 1000 1 (didQopt 0 1000 1) - didV 0 1000 1 (didQstar 0 1000 1) = 1 / 8000 ∧
      didV (1/2) 1000 1 (didQopt (1/2) 1000 1) - didV (1/2) 1000 1 (didQstar (1/2) 1000 1) =
        1 / 4000 := by
  refine ⟨?_, ?_⟩
  · rw [(did_gap 0 1000 1 (by norm_num) (by norm_num)).1]; norm_num
  · rw [(did_gap (1/2) 1000 1 (by norm_num) (by norm_num)).1]; norm_num

/-- `V_B(q)` of a label is `didV` at its stay weight. Source: none: infrastructure. Kind: L -/
theorem did_value_eq_didV : value C (didRouted p h0 h1 L c) = didV p L c ((C ()).w .a) := by
  rw [did_value]; rfl

/-- **The band `1 − c/L ≤ p ≤ 1 − c/(2L)`** (dp-sl-2-009(iv), UNREVIEWED in the source): the
stationary point is in `[0, 1]`, no properly mixed label ties (stay strictly dominates at every
`0 < q < 1`), so pure stay is the only label every supported act of which maximises `e`.
Source: dp-sl-2-009(iv) ("the band … where `V_B` has an interior optimum but no calibrated tie
exists (pure stay is the only calibrated-and-approved label), is the rider the ledger marks
UNREVIEWED"); mandate T6 ("The band (iv) of 2-009 is UNREVIEWED: prove or refute")
Kind: P
Fidelity: exact (general `(L, c)`; "calibrated-and-approved" rendered as `e(flee) < e(stay)` at
every properly mixed label)
Hyps: (a) `0 < L`, `0 < c`, the band -/
theorem did_band (hL : 0 < L) (hc : 0 < c) (hlo : 1 - c / L ≤ p) (hhi : p ≤ 1 - c / (2 * L)) :
    (0 ≤ didQopt p L c ∧ didQopt p L c ≤ 1) ∧
      ∀ C : Proc Unit (fun _ => Act2) ℚ, 0 < (C ()).w .a → 0 < (C ()).w .b →
        didE p h0 h1 L c C .b < didE p h0 h1 L c C .a := by
  have hp1 : p < 1 := by
    have : 0 < c / (2 * L) := by positivity
    linarith
  refine ⟨⟨?_, (did_qopt_le_one_iff p L c hp1 hL).mpr hhi⟩, ?_⟩
  · unfold didQopt
    have : 0 ≤ c / (4 * L * (1 - p)) := by
      apply div_nonneg hc.le; nlinarith
    linarith
  · intro C hqa hqb
    have h := did_e_sub p h0 h1 L c C hqa hqb
    have hs := (C ()).sum_one
    rw [Act2.sum_univ] at hs
    have hq1 : (C ()).w .a < 1 := by linarith
    have hcL : L * (1 - p) ≤ c := by
      have : 1 - p ≤ c / L := by linarith
      rwa [le_div_iff₀ hL, mul_comm] at this
    have : 0 < L * (1 - p) := mul_pos hL (by linarith)
    nlinarith

/-! ### The marginal-holding cf -/

/-- **The marginal-holding (classical) cf**: supposes Death's marginal `q` fixed and values
`(L(1−q), Lq − c)` — `c`-data (a cf stipulation, not a tree quantity).
Source: dp-sl-034 ("the marginal-holding cf ties at `½ + c/(2L)` for every `p`";
`classical_marginal`, `classical_tie`); mandate T6
Kind: D
Fidelity: variant: cf reduced to act values; `Hyps: (c)` the cf's values -/
def didClassicalCf (q : ℚ) : Act2 → ℚ
  | .a => L * (1 - q)
  | .b => L * q - c

/-- The classical cf ties iff `q = ½ + c/(2L)`, for every skill (`L ≠ 0`).
Source: dp-sl-034; mandate T6
Kind: L
Hyps: (c) the cf's values -/
theorem didClassicalCf_tie_iff (hL : L ≠ 0) (q : ℚ) :
    didClassicalCf L c q .a = didClassicalCf L c q .b ↔ q = 1 / 2 + c / (2 * L) := by
  simp only [didClassicalCf]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **At `p = 1` the classical cf agrees with conditioning at no label with `q < 1`**:
conditioning is `(0, −c)` (Death always finds you) while the cf says `(L(1−q), Lq − c)`.
Source: dp-sl-034 ("at `p = 1` the classical marginal-holding cf agrees with no tree referent");
mandate T6
Kind: P
Hyps: (a) `0 < q < 1`, `L ≠ 0`; (c) the cf's values -/
theorem didClassicalCf_ne_e_perfect (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hL : L ≠ 0) :
    didE 1 (by norm_num) (by norm_num) L c C .a = 0 ∧
      didE 1 (by norm_num) (by norm_num) L c C .b = -c ∧
      didClassicalCf L c ((C ()).w .a) .a ≠ didE 1 (by norm_num) (by norm_num) L c C .a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [didE_stay _ _ _ L c C hqa]; ring
  · rw [didE_flee _ _ _ L c C hqb]; ring
  · rw [didE_stay _ _ _ L c C hqa]
    simp only [didClassicalCf]
    have hs := (C ()).sum_one
    rw [Act2.sum_univ] at hs
    have : (C ()).w .a < 1 := by linarith
    intro h
    have : L * (1 - (C ()).w .a) = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp this with h' | h'
    · exact hL h'
    · linarith

end tree

end Cleanroom.Decision.DpDutchBook
