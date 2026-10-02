import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T10 — Skyrms's Ratifiability Lemma

[[dp-calib-limits-mandate]] T10 (dp-sl-040; Skyrms 1990, "Ratifiability and the logic of
decision", lines 116–119 (R′) and 290–322 of the OCR text, which is garbled — the statement is
reconstructed from that window plus (R′)).

Setting: a finite probability space `pr : FinDistr K W`, finitely many acts `A`, an information
partition `e : W → E` (the experimental result), the act as a function of the result
`act : E → A` (this *is* "knows which act she will choose for every possible experimental
result", rendered as measurability), Savage utility `u : A → W → K`, and the conditional Savage
expected utility `savageEU pr u F a = (∑_{w ∈ F} pr(w) u(a, w)) / pr(F)`. Ratifiability (R′):
`a` is ratifiable iff, when `pr(act ∘ e = a) > 0`, `a` maximises `savageEU` conditional on its
own act event. The act event `{act ∘ e = a}` is the union of the cells `e⁻¹(ε)` with
`act ε = a` — "conditioning on an act = conditioning on the union of the cells with
`pr(A | e) = 1`" is the definition of the act event here.

**Ratifiability Lemma** (`ratifiability_lemma`): if `act ε` maximises `savageEU` conditional on
every positive cell, then every act is ratifiable. Proof = the "algebraic property of Savage
expected utility": the numerator over a disjoint union of cells is the sum of the numerators
over the cells (`sum_actEvent_eq`), maximising on each cell of `{act ∘ e = a}` maximises on
the union; null cells contribute `0`. Corollary (`prob_eq_zero_of_not_ratifiable`): an act that
fails ratifiability's maximisation clause has probability `0`. Note (no theorem): v2 runs the
derivation in the opposite direction — self-knowledge from calibration + recording
(`selfTransparent_of_recordsFor_strict`), ratifiability from optimality.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Decision.DpCalibration
open Finset

section skyrms

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {W E A : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] [Fintype A]
  [DecidableEq A]

/-- The cell `e⁻¹(ε)` of the information partition.
Source: Skyrms 1990 line ~300 ("each member of the information partition `e`")
Kind: D -/
def cell (e : W → E) (ε : E) : Finset W := Finset.univ.filter fun w => e w = ε

/-- The act event `{act ∘ e = a}`: the union of the cells on which the agent chooses `a`.
Source: Skyrms 1990 line ~305 ("conditioning on an act `A` is equivalent to conditioning on the
union of the members `e` of the information partition such that `pr(A | e) = 1`")
Kind: D
Fidelity: variant: knowledge rendered as measurability (`act` is a function of the result) -/
def actEvent (e : W → E) (act : E → A) (a : A) : Finset W :=
  Finset.univ.filter fun w => act (e w) = a

/-- Savage expected utility conditional on an event `F`: `(∑_{w ∈ F} pr(w) u(a, w)) / pr(F)`.
Source: Skyrms 1990 (R′) ("the Savage expected utility conditional on it")
Kind: D -/
def savageEU (pr : FinDistr K W) (u : A → W → K) (F : Finset W) (a : A) : K :=
  (∑ w ∈ F, pr.w w * u a w) / probOf pr F

/-- **Ratifiability (R′)**: if `a` has positive probability of being chosen, `a` maximises Savage
expected utility conditional on its own act event.
Source: Skyrms 1990 line 119, (R′) ("`A_i` is ratifiable iff `V(A_i) ≥ U(A_j | A_i)` for all
`j`"; `V(A_i) = U(A_i | A_i)` by (E)); Jeffrey
Kind: D
Fidelity: variant: knowledge as measurability; the act event as the union of the cells -/
def Ratifiable (pr : FinDistr K W) (e : W → E) (act : E → A) (u : A → W → K) (a : A) : Prop :=
  0 < probOf pr (actEvent e act a) →
    ∀ a', savageEU pr u (actEvent e act a) a' ≤ savageEU pr u (actEvent e act a) a

/-- **The lemma's hypothesis**: on every positive cell the chosen act maximises conditional
Savage expected utility ("she will receive an experimental result, condition on it, and then
choose an act which maximizes expected utility").
Source: Skyrms 1990 lines 293–298 (the Ratifiability Lemma's hypothesis)
Kind: D -/
def MaximizesOnCells (pr : FinDistr K W) (e : W → E) (act : E → A) (u : A → W → K) : Prop :=
  ∀ ε, 0 < probOf pr (cell e ε) →
    ∀ a', savageEU pr u (cell e ε) a' ≤ savageEU pr u (cell e ε) (act ε)

/-- The act event is the disjoint union of the cells on which `act` chooses `a`: a sum over it
is the sum over those cells. Source: Skyrms 1990 line ~305. Kind: L -/
theorem sum_actEvent_eq (e : W → E) (act : E → A) (a : A) (f : W → K) :
    ∑ w ∈ actEvent e act a, f w =
      ∑ ε ∈ Finset.univ.filter (fun ε => act ε = a), ∑ w ∈ cell e ε, f w := by
  unfold actEvent cell
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_fiberwise Finset.univ e (fun w => if act (e w) = a then f w else 0)]
  refine Finset.sum_congr rfl fun ε _ => ?_
  by_cases h : act ε = a
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mem_filter] at hw
    rw [if_pos (by rw [hw.2]; exact h)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [if_neg (by rw [hw.2]; exact h)]

/-- **The Ratifiability Lemma** (Skyrms 1990): if the decision-maker will condition on the
experimental result and then choose an act maximising conditional Savage expected utility,
and she knows which act she will choose for every result (`act`), then every act is
ratifiable. Proof: the "algebraic property of Savage expected utility" — over the disjoint
union of the cells of `{act ∘ e = a}` the numerator is the sum of the cell numerators, each
of which `a` maximises (null cells contribute `0`), so `a` maximises on the union.
Source: Skyrms 1990, lines 293–320 (the Ratifiability Lemma and its proof; OCR-garbled window);
dp-sl-040
Kind: P
Fidelity: variant: knowledge rendered as measurability (`act : E → A`) and as the hypothesis
`MaximizesOnCells`; "conditioning on an act = conditioning on the union of the cells" is the
definition of `actEvent`
Hyps: (a) `MaximizesOnCells` (the lemma's hypothesis) -/
theorem ratifiability_lemma (pr : FinDistr K W) (e : W → E) (act : E → A) (u : A → W → K)
    (hmax : MaximizesOnCells pr e act u) (a : A) : Ratifiable pr e act u a := by
  intro hpos a'
  unfold savageEU
  rw [div_le_div_iff_of_pos_right hpos, sum_actEvent_eq, sum_actEvent_eq]
  apply Finset.sum_le_sum
  intro ε hε
  rw [Finset.mem_filter] at hε
  by_cases hc : 0 < probOf pr (cell e ε)
  · have := hmax ε hc a'
    unfold savageEU at this
    rw [div_le_div_iff_of_pos_right hc, hε.2] at this
    exact this
  · have hz : probOf pr (cell e ε) = 0 := le_antisymm (not_lt.mp hc) (probOf_nonneg pr _)
    have h0 : ∀ w ∈ cell e ε, pr.w w = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => pr.nonneg w).mp hz
    rw [Finset.sum_eq_zero fun w hw => by rw [h0 w hw, zero_mul],
      Finset.sum_eq_zero fun w hw => by rw [h0 w hw, zero_mul]]

/-- **Contrapositive corollary**: an act failing ratifiability's maximisation clause has
probability `0` of being chosen ("non-ratifiable acts get probability `0` at `t₀`").
Source: Skyrms 1990 line ~318 ("By contraposition, non-ratifiable acts get probability 0")
Kind: C
Fidelity: exact (in the variant setting)
Hyps: (a) `MaximizesOnCells` -/
theorem prob_eq_zero_of_not_ratifiable (pr : FinDistr K W) (e : W → E) (act : E → A)
    (u : A → W → K) (hmax : MaximizesOnCells pr e act u) (a : A)
    (h : ¬ ∀ a', savageEU pr u (actEvent e act a) a' ≤ savageEU pr u (actEvent e act a) a) :
    probOf pr (actEvent e act a) = 0 := by
  by_contra hne
  have hpos : 0 < probOf pr (actEvent e act a) :=
    lt_of_le_of_ne (probOf_nonneg pr _) (Ne.symm hne)
  exact h (ratifiability_lemma pr e act u hmax a hpos)

end skyrms

/-! ## N+: two cells, two acts, a genuine maximisation -/

/-- The fair distribution on `Bool`. Source: none: infrastructure. Kind: D -/
def fairBool : FinDistr ℚ Bool where
  w _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The two-cell instance: result `= world` (`e = id`), the agent chooses `a` on `true` and `b` on
`false`, utility `1` for matching the world (`a` on `true`, `b` on `false`) and `0` otherwise.
Source: mandate T10 (witness design)
Kind: D -/
def skyrmsU : Act2 → Bool → ℚ
  | .a, true => 1
  | .a, false => 0
  | .b, true => 0
  | .b, false => 1

/-- The chosen act on each result. Source: mandate T10. Kind: D -/
def skyrmsAct : Bool → Act2 := fun b => if b then .a else .b

/-- `savageEU` on the two-cell instance: on cell `true` the act `a` is worth `1`, `b` worth `0`;
symmetrically on `false`. Source: mandate T10. Kind: L -/
theorem skyrms_cell_values :
    savageEU fairBool skyrmsU (cell id true) .a = 1 ∧ savageEU fairBool skyrmsU (cell id true) .b = 0 ∧
    savageEU fairBool skyrmsU (cell id false) .a = 0 ∧ savageEU fairBool skyrmsU (cell id false) .b = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [savageEU, cell, probOf, fairBool, skyrmsU, Finset.sum_filter, Fintype.sum_bool,
      Finset.filter_eq'] <;> norm_num

/-- **The hypothesis package is inhabited with a genuine maximisation** (`1 > 0` on each cell),
and the lemma's conclusion is checked: both acts are ratifiable, each act event being its own
cell. Source: mandate T10 (N+). Kind: N+. Fidelity: exact. Hyps: none -/
theorem skyrms_instance :
    MaximizesOnCells fairBool id skyrmsAct skyrmsU ∧
    (∀ a, Ratifiable fairBool id skyrmsAct skyrmsU a) ∧
    savageEU fairBool skyrmsU (cell id true) .b < savageEU fairBool skyrmsU (cell id true) .a := by
  obtain ⟨h1, h2, h3, h4⟩ := skyrms_cell_values
  have hmax : MaximizesOnCells fairBool id skyrmsAct skyrmsU := by
    intro ε _ a'
    cases ε <;> cases a' <;> simp [skyrmsAct, h1, h2, h3, h4]
  exact ⟨hmax, fun a => ratifiability_lemma _ _ _ _ hmax a, by rw [h1, h2]; norm_num⟩

end Cleanroom.Decision.DpCalibLimits
