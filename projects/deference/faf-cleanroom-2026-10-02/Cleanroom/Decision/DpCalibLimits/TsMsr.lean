import Cleanroom.Decision.DpCalibLimits.Family
import Cleanroom.Decision.DpCalibLimits.MiniatureTS

/-!
# T4(c), unguarded — TS ⊄ MSR: a test-sequence limit whose uniform-ray values reverse

[[dp-calib-limits-mandate]] T4(c) (SE-18′(b) Open: "whether a fixed-point family realizes the
reversal"; S10 / C2-9′ assert `TS ⊆ MSR`).

**The tree** `tsTree` (five points, eight leaves): a fair coin; on the left, point `e` whose
first act leads to a `d`-copy (`a ↦ 10, b ↦ 0`) and whose second act leads to a copy of the
same payoffs carried by a *different* point `g`; on the right, point `f` whose first act leads
to a `d`-copy (`a ↦ 0, b ↦ 30`) and whose second act leads to a point `h` both of whose acts
pay `30`. `O_d` = the four `d`-copy worlds.

**The test sequence** `tsProc ε` (`e ↦ (2ε, 1 − 2ε)`, `f ↦ δ_b`, `d, g ↦ δ_a`, `h ↦ δ_b`) at
`ε_n = 1/(n+2)`: under the tremble at `ε` the entry weights to `d` are `s = (1 − ε)·2ε + ε/2`
on the left and `t = ε/2` on the right, so `a` is the best reply at `d` (`10s ≥ 30t` iff
`ε ≤ ½`); at `e` both acts tie exactly for every `ε` (the `g`-copy trembles like the `d`-copy),
so the moving coordinate `2ε` is approved; at `f`, `g`, `h` the supported act is a best reply.
The limit `C₀ = tsProc 0` has `O_d` unrealized, and along Definition 10's uniform ray the values
at `d` are `(5, 15)`: the argmax is `{b}`, but `supp C₀(d) = {a}`. So `C₀ ∈ TS ∖ MSR`
(`ts_not_msr`): the sources' second inclusion is **refuted**, and SE-18′(b)'s Open is settled
affirmatively — a fixed-point family does realize the reversal. The guarded inclusion
(`msrAt_of_ts_of_realized`) is the surviving neighbour.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- The five points. Source: mandate T4(c) (a modification of the two-route tree). Kind: D -/
inductive TsPt : Type
  | d
  | e
  | f
  | g
  | h
  deriving DecidableEq, Fintype

instance : Nonempty TsPt := ⟨.d⟩

/-- The eight worlds: `(route, act)` on the `d`-copies, and on the alternative copies.
Source: mandate T4(c). Kind: D -/
inductive TsW : Type
  | la
  | lb
  | ra
  | rb
  | ga
  | gb
  | ha
  | hb
  deriving DecidableEq, Fintype

/-- The route's entry point (`e` left, `f` right). Source: mandate T4(c). Kind: D -/
def tsPt (i : Fin 2) : TsPt := if i = 0 then .e else .f

/-- The route's alternative point (`g` left, `h` right). Source: mandate T4(c). Kind: D -/
def tsAlt (i : Fin 2) : TsPt := if i = 0 then .g else .h

/-- The `d`-copy world on route `i` after act `x`. Source: mandate T4(c). Kind: D -/
def tsW (i : Fin 2) (x : Act2) : TsW :=
  if i = 0 then (if x = .a then .la else .lb) else (if x = .a then .ra else .rb)

/-- The alternative copy's world on route `i` after act `x`. Source: mandate T4(c). Kind: D -/
def tsWAlt (i : Fin 2) (x : Act2) : TsW :=
  if i = 0 then (if x = .a then .ga else .gb) else (if x = .a then .ha else .hb)

/-- The `d`-copy payoffs: left `a ↦ 10, b ↦ 0`, right `a ↦ 0, b ↦ 30`.
Source: SE-18′(b). Kind: D -/
def tsPay (i : Fin 2) (x : Act2) : ℚ :=
  if i = 0 then (if x = .a then 10 else 0) else (if x = .a then 0 else 30)

/-- The alternative copies' payoffs: left as the `d`-copy (`10`, `0`), right `30` on both.
Source: mandate T4(c) ("the vanishing coordinates at `e`/`f` sit at exact ties"). Kind: D -/
def tsPayAlt (i : Fin 2) (x : Act2) : ℚ :=
  if i = 0 then (if x = .a then 10 else 0) else 30

/-- **The TS ⊄ MSR tree**. Source: mandate T4(c); SE-18′(b). Kind: D -/
def tsTree : Tree TsW TsPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision (tsPt i) fun
      | .a => .decision .d fun x => .leaf (tsW i x) (tsPay i x)
      | .b => .decision (tsAlt i) fun x => .leaf (tsWAlt i x) (tsPayAlt i x)

/-- Observations: `O_d` = the `d`-copy worlds; `O_e = O_f = ⊤`; `O_g`, `O_h` = their copies.
Source: mandate T4(c). Kind: D -/
def tsObs : TsPt → Finset TsW
  | .d => {.la, .lb, .ra, .rb}
  | .e => Finset.univ
  | .f => Finset.univ
  | .g => {.ga, .gb}
  | .h => {.ha, .hb}

/-- Action events by the world's act coordinate (for `e`, `f`: the subtree).
Source: mandate T4(c). Kind: D -/
def tsActEv : (p : TsPt) → Act2 → Finset TsW
  | .d, .a => {.la, .ra}
  | .d, .b => {.lb, .rb}
  | .e, .a => {.la, .lb}
  | .e, .b => {.ga, .gb}
  | .f, .a => {.ra, .rb}
  | .f, .b => {.ha, .hb}
  | .g, .a => {.ga}
  | .g, .b => {.gb}
  | .h, .a => {.ha}
  | .h, .b => {.hb}

/-- A sum over the leaves. Source: none: infrastructure. Kind: L -/
theorem tsTree_sum {M : Type} [AddCommMonoid M] (f : tsTree.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ x : Act2, f ⟨i, .a, x, ()⟩) + ∑ x : Act2, f ⟨i, .b, x, ()⟩) := by
  unfold tsTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, sum_leaves_decision]
  simp only [Tree.sum_leaves_leaf]

/-- The fixed-point family `tsProc ε`: `e ↦ (2ε, 1 − 2ε)`, `f ↦ δ_b`, `d, g ↦ δ_a`, `h ↦ δ_b`.
Source: mandate T4(c). Kind: D -/
def tsProc (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : Proc TsPt (fun _ => Act2) ℚ
  | .d => FinDistr.pure .a
  | .e => FinDistr.act2 (2 * ε) (by linarith) (by linarith)
  | .f => FinDistr.pure .b
  | .g => FinDistr.pure .a
  | .h => FinDistr.pure .b

/-- The limit `C₀ = tsProc 0`. Source: mandate T4(c). Kind: D -/
def tsC0 : Proc TsPt (fun _ => Act2) ℚ := tsProc 0 le_rfl (by norm_num)

section trembleValues

variable (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2)

/-- The trembled procedure along the family. Source: none: infrastructure. Kind: D -/
noncomputable abbrev tsTr : Proc TsPt (fun _ => Act2) ℚ :=
  tremble (tsProc ε h0.le h1) ε h0.le (by linarith)

local macro "ts_eval" : tactic =>
  `(tactic| (simp [tsTree, leafLaw, tsW, tsWAlt, tsPt, tsAlt, tsPay, tsPayAlt, tsProc, tsObs, tsActEv,
      tremble_w, act2_card_rat, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair, FinDistr.coin]; try ring))

/-- `ν` and `paySum` of the `d`-acts within `O_d` under the tremble. Kind: L. Source: mandate T4(c). -/
theorem tsTr_d :
    nu (tsTr ε h0 h1) tsTree (tsActEv .d .a ∩ tsObs .d) = (1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2 +
        (1 - ε / 2) * (ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .d .a ∩ tsObs .d) =
        10 * ((1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2) ∧
    nu (tsTr ε h0 h1) tsTree (tsActEv .d .b ∩ tsObs .d) = (ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2 +
        (ε / 2) * (ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .d .b ∩ tsObs .d) = 30 * ((ε / 2) * (ε / 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval

/-- `ν` and `paySum` of the `e`-acts under the tremble. Kind: L. Source: mandate T4(c). -/
theorem tsTr_e :
    nu (tsTr ε h0 h1) tsTree (tsActEv .e .a ∩ tsObs .e) = (ε * (2 - 2 * ε) + ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .e .a ∩ tsObs .e) =
        10 * ((1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2) ∧
    nu (tsTr ε h0 h1) tsTree (tsActEv .e .b ∩ tsObs .e) = (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .e .b ∩ tsObs .e) =
        10 * ((1 - ε / 2) * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval

/-- `ν` and `paySum` of the `f`-acts under the tremble. Kind: L. Source: mandate T4(c). -/
theorem tsTr_f :
    nu (tsTr ε h0 h1) tsTree (tsActEv .f .a ∩ tsObs .f) = (ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .f .a ∩ tsObs .f) = 30 * ((ε / 2) * (ε / 2) / 2) ∧
    nu (tsTr ε h0 h1) tsTree (tsActEv .f .b ∩ tsObs .f) = (1 - ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .f .b ∩ tsObs .f) = 30 * ((1 - ε / 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval

/-- `ν` and `paySum` of the `g`-acts under the tremble. Kind: L. Source: mandate T4(c). -/
theorem tsTr_g :
    nu (tsTr ε h0 h1) tsTree (tsActEv .g .a ∩ tsObs .g) =
        (1 - ε / 2) * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .g .a ∩ tsObs .g) =
        10 * ((1 - ε / 2) * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2) ∧
    nu (tsTr ε h0 h1) tsTree (tsActEv .g .b ∩ tsObs .g) =
        (ε / 2) * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .g .b ∩ tsObs .g) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval

/-- `ν` and `paySum` of the `h`-acts under the tremble. Kind: L. Source: mandate T4(c). -/
theorem tsTr_h :
    nu (tsTr ε h0 h1) tsTree (tsActEv .h .a ∩ tsObs .h) = (ε / 2) * (1 - ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .h .a ∩ tsObs .h) = 30 * ((ε / 2) * (1 - ε / 2) / 2) ∧
    nu (tsTr ε h0 h1) tsTree (tsActEv .h .b ∩ tsObs .h) = (1 - ε / 2) * (1 - ε / 2) / 2 ∧
    paySum (tsTr ε h0 h1) tsTree (tsActEv .h .b ∩ tsObs .h) = 30 * ((1 - ε / 2) * (1 - ε / 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval
  · rw [nu_eq_sum, tsTree_sum]; ts_eval
  · rw [paySum_eq_sum_ite, tsTree_sum]; ts_eval

end trembleValues

/-- **The D2 condition at `ε` for `tsProc ε`**, at every point of the tree.
Source: mandate T4(c); SE-18′(b)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ ½` -/
theorem tsProc_d2At (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    D2At tsObs tsActEv tsTree (tsProc ε h0.le h1) ε h0 (by linarith) := by
  intro p _ _ _ a ha
  have hs : 0 < ε * (2 - 2 * ε) + ε / 2 := by nlinarith
  have hs1 : ε * (2 - 2 * ε) + ε / 2 < 1 := by nlinarith
  have hp : 0 < 1 - ε / 2 := by linarith
  cases p
  · -- d
    obtain ⟨na, pa, nb, pb⟩ := tsTr_d ε h0 h1
    cases a
    · refine ⟨by rw [na]; positivity, fun b _ => ?_⟩
      cases b
      · exact le_rfl
      · simp only [condExp]
        rw [na, pa, nb, pb, div_le_div_iff₀ (by positivity) (by positivity)]
        have key : 10 * ((1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2) *
            (ε / 2 * (ε * (2 - 2 * ε) + ε / 2) / 2 + ε / 2 * (ε / 2) / 2) -
            30 * (ε / 2 * (ε / 2) / 2) *
            ((1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2) / 2 + (1 - ε / 2) * (ε / 2) / 2) =
            (1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2 + ε / 2) * ε ^ 2 * (5 * (1 - 2 * ε) / 4) := by
          ring
        have hprod : 0 ≤ (1 - ε / 2) * (ε * (2 - 2 * ε) + ε / 2 + ε / 2) * ε ^ 2 *
            (5 * (1 - 2 * ε) / 4) :=
          mul_nonneg (mul_nonneg (mul_nonneg hp.le (by linarith)) (sq_nonneg _)) (by linarith)
        linarith
    · simp [tsProc] at ha
  · -- e
    obtain ⟨na, pa, nb, pb⟩ := tsTr_e ε h0 h1
    have hcmp : condExp (tsTr ε h0 h1) tsTree (tsActEv .e .b ∩ tsObs .e) =
        condExp (tsTr ε h0 h1) tsTree (tsActEv .e .a ∩ tsObs .e) := by
      simp only [condExp]
      rw [na, pa, nb, pb, div_eq_div_iff (div_pos (by linarith) two_pos).ne'
        (div_pos hs two_pos).ne']
      ring
    cases a
    · refine ⟨by rw [na]; positivity, fun b _ => ?_⟩
      cases b
      · exact le_rfl
      · exact hcmp.le
    · refine ⟨by rw [nb]; positivity, fun b _ => ?_⟩
      cases b
      · exact hcmp.ge
      · exact le_rfl
  · -- f
    obtain ⟨na, pa, nb, pb⟩ := tsTr_f ε h0 h1
    cases a
    · simp [tsProc] at ha
    · refine ⟨by rw [nb]; positivity, fun b _ => ?_⟩
      cases b
      · simp only [condExp]
        rw [na, pa, nb, pb, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      · exact le_rfl
  · -- g
    obtain ⟨na, pa, nb, pb⟩ := tsTr_g ε h0 h1
    cases a
    · refine ⟨by rw [na]; exact div_pos (mul_pos hp (by linarith)) two_pos, fun b _ => ?_⟩
      cases b
      · exact le_rfl
      · simp only [condExp]
        have h1s : 0 < 1 - (ε * (2 - 2 * ε) + ε / 2) := by linarith
        rw [na, pa, nb, pb, div_le_div_iff₀ (by positivity) (by positivity)]
        have hpa : 0 < 10 * ((1 - ε / 2) * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2) :=
          mul_pos (by norm_num) (div_pos (mul_pos hp h1s) two_pos)
        have hnb : 0 < ε / 2 * (1 - (ε * (2 - 2 * ε) + ε / 2)) / 2 :=
          div_pos (mul_pos (by positivity) h1s) two_pos
        nlinarith [mul_pos hpa hnb]
    · simp [tsProc] at ha
  · -- h
    obtain ⟨na, pa, nb, pb⟩ := tsTr_h ε h0 h1
    cases a
    · simp [tsProc] at ha
    · refine ⟨by rw [nb]; positivity, fun b _ => ?_⟩
      cases b
      · simp only [condExp]
        rw [na, pa, nb, pb, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      · exact le_rfl

/-- **`C₀` is test-sequence tremble-EDT-consistent** along `ε_n = 1/(n+2)`,
`C_n = tsProc ε_n`. Source: mandate T4(c). Kind: P. Fidelity: exact. Hyps: none -/
theorem tsC0_ts : TS tsObs tsActEv tsC0 tsTree := by
  refine ⟨fun n => 1 / ((n : ℚ) + 2),
    fun n => tsProc (1 / ((n : ℚ) + 2)) (by positivity) (one_div_add_two_le_half n),
    fun n => ⟨by positivity, by linarith [one_div_add_two_le_half n]⟩, ?_, ?_, ?_⟩
  · intro δ hδ
    exact one_div_add_two_tendsto δ hδ
  · intro p a δ hδ
    obtain ⟨N, hN⟩ := one_div_add_two_tendsto (δ / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hlt := hN n hn
    have hpos : (0 : ℚ) < 1 / ((n : ℚ) + 2) := by positivity
    (cases p <;> cases a <;> simp [tsProc, tsC0, hδ]) <;>
      (rw [abs_of_pos (by positivity)]; rw [one_div] at hlt; linarith)
  · intro n
    exact tsProc_d2At _ (by positivity) (one_div_add_two_le_half n)

/-- `coeff 2 p = (derivative (derivative p)).eval 0 / 2`. Source: none: infrastructure. Kind: L -/
theorem coeff_two_eq_eval_zero_derivative (p : Polynomial ℚ) :
    p.coeff 2 = (Polynomial.derivative (Polynomial.derivative p)).eval 0 / 2 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
  norm_num

/-- A polynomial with `coeff 0 = coeff 1 = 0` and `coeff 2 ≠ 0` has order `2`.
Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_eq_two_of_coeff {p : Polynomial ℚ} (h0 : p.coeff 0 = 0)
    (h1 : p.coeff 1 = 0) (h2 : p.coeff 2 ≠ 0) : p.natTrailingDegree = 2 := by
  have hne : p ≠ 0 := fun h => h2 (by rw [h, Polynomial.coeff_zero])
  refine le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero h2) ?_
  apply Polynomial.le_natTrailingDegree hne
  intro m hm
  have : m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl
  · exact h0
  · exact h1

/-- The uniform-ray limit value from an order-`2` event polynomial.
Source: none: infrastructure. Kind: L -/
theorem limitVal_of_coeff_two (C : Proc TsPt (fun _ => Act2) ℚ) (Y : Finset TsW)
    (h0 : (nuPoly C tsTree Y).coeff 0 = 0) (h1 : (nuPoly C tsTree Y).coeff 1 = 0)
    (h2 : (nuPoly C tsTree Y).coeff 2 ≠ 0) :
    limitVal C tsTree Y = (payPoly C tsTree Y).coeff 2 / (nuPoly C tsTree Y).coeff 2 := by
  unfold limitVal
  rw [natTrailingDegree_eq_two_of_coeff h0 h1 h2]

section limitValues

local macro "ts_peval" : tactic =>
  `(tactic| (simp [tsTree, leafLawPoly, trembleW, tsW, tsWAlt, tsPt, tsAlt, tsPay, tsPayAlt, tsProc, tsC0, tsObs, tsActEv, act2_card_rat, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair, FinDistr.coin]; try norm_num))

/-- The uniform-ray coefficients of `C₀` at `d`: the `a`-event has order `1` with
`limitVal = 5`, the `b`-event order `2` with `limitVal = 15`. Kind: L. Source: SE-18′(b). -/
theorem tsC0_coeffs :
    (nuPoly tsC0 tsTree (tsActEv .d .a ∩ tsObs .d)).coeff 0 = 0 ∧
    (nuPoly tsC0 tsTree (tsActEv .d .a ∩ tsObs .d)).coeff 1 = 1 / 2 ∧
    (payPoly tsC0 tsTree (tsActEv .d .a ∩ tsObs .d)).coeff 1 = 5 / 2 ∧
    (nuPoly tsC0 tsTree (tsActEv .d .b ∩ tsObs .d)).coeff 0 = 0 ∧
    (nuPoly tsC0 tsTree (tsActEv .d .b ∩ tsObs .d)).coeff 1 = 0 ∧
    (nuPoly tsC0 tsTree (tsActEv .d .b ∩ tsObs .d)).coeff 2 = 1 / 4 ∧
    (payPoly tsC0 tsTree (tsActEv .d .b ∩ tsObs .d)).coeff 2 = 15 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [coeff_two_eq_eval_zero_derivative, nuPoly_eq_sum, tsTree_sum]; ts_peval
  · rw [coeff_two_eq_eval_zero_derivative, payPoly_eq_sum, tsTree_sum]; ts_peval

end limitValues

/-- **`C₀` is not MSR at `d`**: along Definition 10's uniform ray the act values at `d` are
`5` for `a` and `15` for `b`, and `supp C₀(d) = {a}`.
Source: SE-18′(b) (the `(5, 15)` values); mandate T4(c)
Kind: P
Fidelity: exact
Hyps: none -/
theorem tsC0_not_msrAt : ¬ MSRAt tsObs tsActEv tsC0 tsTree .d := by
  obtain ⟨a0, a1, ap1, b0, b1, b2, bp2⟩ := tsC0_coeffs
  intro h
  have ha : 0 < (tsC0 .d).w .a := by simp [tsC0, tsProc]
  have hbne : nuPoly tsC0 tsTree (tsActEv .d .b ∩ tsObs .d) ≠ 0 := fun hz => by
    rw [hz, Polynomial.coeff_zero] at b2; norm_num at b2
  have hle := (h .a ha).2 .b hbne
  rw [limitVal_of_coeff_one _ _ _ a0 (by rw [a1]; norm_num), ap1, a1,
    limitVal_of_coeff_two _ _ b0 b1 (by rw [b2]; norm_num), bp2, b2] at hle
  norm_num at hle

/-- `d` is queried on `tsTree`. Source: none: infrastructure. Kind: L -/
theorem tsTree_d_queried : TsPt.d ∈ queried tsTree := by
  unfold tsTree
  rw [queried_chance, Finset.mem_biUnion]
  refine ⟨0, Finset.mem_univ _, ?_⟩
  rw [queried_decision, Finset.mem_insert]
  right
  rw [Finset.mem_biUnion]
  exact ⟨.a, Finset.mem_univ _, by rw [queried_decision]; exact Finset.mem_insert_self _ _⟩


/-- **TS ⊄ MSR**: `C₀` is test-sequence tremble-EDT-consistent on `tsTree` (`tsC0_ts`) and
not mixed-strategy ratifiable at the queried point `d` (`tsC0_not_msrAt`); `O_d` is
`C₀`-unrealized. This refutes S10 / C2-9′'s "`TS ⊆ MSR`" as stated and settles SE-18′(b)'s
Open ("whether a fixed-point family realizes the reversal") affirmatively; the guarded
inclusion `msrAt_of_ts_of_realized` is the surviving neighbour.
Source: S10 / C2-9′ ("`FF ⊆ TS ⊆ MSR` [derived]") — refuted; SE-18′(b) (Open) — settled;
P04 Open 11; dp-sl-005
Kind: N+
Fidelity: exact
Hyps: none -/
theorem ts_not_msr :
    TS tsObs tsActEv tsC0 tsTree ∧ TsPt.d ∈ queried tsTree ∧ ¬ MSR tsObs tsActEv tsC0 tsTree :=
  ⟨tsC0_ts, tsTree_d_queried, fun h => tsC0_not_msrAt (h .d tsTree_d_queried)⟩

end Cleanroom.Decision.DpCalibLimits
