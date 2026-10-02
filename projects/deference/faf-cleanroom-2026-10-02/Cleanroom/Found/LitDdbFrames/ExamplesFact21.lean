import Cleanroom.Found.LitDdbFrames.Value
import Mathlib.Data.Fin.VecNotation

/-!
# Witnesses on three worlds: Fact 2.1 and Figure 5's `F₂`

Package `lit-ddb-frames`, Target 20 and the fn 52 verdict (`lit-ddb-frames-findings.md` F3).
Fact 2.1 is DDB's key counterexample (trusted but not valued); here its Value/Total-Trust
failure and the resulting `π ∉ convexHull C_π` are proved — the hull half of the fourth
condition failing, as opposed to Figure 2 where the modest-informedness half fails. Figure 5's
`F₂` with fn 52's variable `X = (5, −1, −10)` gives the second kind of failure on three worlds:
`P_2` is not modestly informed, and the cut `{E(X) ≥ 0}` witnesses it.

Trust for Fact 2.1 (DDB's Mathematica check) is *not* proved here (stretch; see the report).
-/

namespace Cleanroom.Found.LitDdbFrames.Examples

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-- A three-world frame from its rows.
Source: none: infrastructure (Target 20)
Kind: D
Fidelity: n/a -/
def mk3 (r₀ r₁ r₂ : Fin 3 → ℝ) (h₀ : r₀ ∈ stdSimplex ℝ (Fin 3)) (h₁ : r₁ ∈ stdSimplex ℝ (Fin 3))
    (h₂ : r₂ ∈ stdSimplex ℝ (Fin 3)) : Frame (Fin 3) where
  P := ![r₀, r₁, r₂]
  P_mem := fun w => by fin_cases w <;> assumption

/-- The third coordinate of a three-vector (not in the default simp set).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

/-- `fin_cases` leaves `⟨2, _⟩`; this rewrites it to the literal `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fin3_mk_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

/-- A nonnegative triple summing to one is a distribution on three worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem simplex3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    (![a, b, c] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) :=
  ⟨fun x => by fin_cases x <;> simp [ha, hb, hc], by simp [Fin.sum_univ_three, vec3_two, fin3_mk_two, h]⟩

/-! ## Fact 2.1 (Target 20) -/

/-- Fact 2.1's frame: rows `(0.45, 0.10, 0.45)`, `(0.15, 0.70, 0.15)`, `(0.30, 0.10, 0.60)`.
Source: [[Deference Done Better]] §2 l. 164
Kind: D
Fidelity: exact -/
def fact21 : Frame (Fin 3) :=
  mk3 ![45 / 100, 10 / 100, 45 / 100] ![15 / 100, 70 / 100, 15 / 100] ![30 / 100, 10 / 100, 60 / 100]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Fact 2.1's rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fact21_P : fact21.P 0 = ![45 / 100, 10 / 100, 45 / 100] ∧
    fact21.P 1 = ![15 / 100, 70 / 100, 15 / 100] ∧ fact21.P 2 = ![30 / 100, 10 / 100, 60 / 100] :=
  ⟨rfl, rfl, rfl⟩

/-- Fact 2.1's deferrer `π = (0.17, 0.56, 0.27)`.
Source: [[Deference Done Better]] §2 l. 163
Kind: D
Fidelity: exact -/
def π21 : Fin 3 → ℝ := ![17 / 100, 56 / 100, 27 / 100]

/-- `π21` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π21_mem : π21 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Fact 2.1's option `O_1 = (29, −3, −13)`.
Source: [[Deference Done Better]] §2 l. 165
Kind: D
Fidelity: exact -/
def O1 : Fin 3 → ℝ := ![29, -3, -13]

/-- The expectations of `O_1`: `6.9`, `0.3`, `0.6` at the three candidates, `−0.26` under `π`.
Source: [[Deference Done Better]] §2 l. 165; item 056 (arithmetic)
Kind: L
Fidelity: exact -/
theorem fact21_E_O1 :
    E (fact21.P 0) O1 = 69 / 10 ∧ E (fact21.P 1) O1 = 3 / 10 ∧ E (fact21.P 2) O1 = 3 / 5 ∧
      E π21 O1 = -13 / 50 := by
  obtain ⟨h0, h1, h2⟩ := fact21_P
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, π21, O1]

/-- **Target 20 (Fact 2.1), Total Trust fails** at `(O_1, 0)` in product form: every candidate
has `E(O_1) ≥ 0`, so the event is everything and the product sum is `E_π(O_1) = −0.26 < 0`.
Source: [[Deference Done Better]] §2 l. 161–165, l. 206
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_not_totalTrust : ¬ TotalTrust π21 fact21 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fact21_P
  have hsum := h.event_sum O1 0
  have hev : fact21.estEvent O1 0 = univ := by
    ext w
    fin_cases w <;> norm_num [Frame.mem_estEvent, E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, O1]
  rw [hev] at hsum
  norm_num [Fin.sum_univ_three, vec3_two, fin3_mk_two, π21, O1] at hsum

/-- **Target 20 (Fact 2.1), Value fails** directly: on `{O_0 = 0, O_1}` the only recommended
strategy takes `O_1` everywhere, and `E_π(O_1) = −0.26 < 0 = E_π(O_0)`.
Source: [[Deference Done Better]] §2 l. 165
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_not_value : ¬ Value π21 fact21 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fact21_P
  have hrec : fact21.Recommended {fun _ => 0, O1} (fun _ => O1) := by
    refine ⟨⟨fun w => by simp, fun _ _ _ => rfl⟩, fun w o ho => ?_⟩
    simp only [mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · rw [E_const (fact21.P_mem w)]
      fin_cases w <;> norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, O1]
    · exact le_rfl
  have := h _ (insert_nonempty _ _) _ hrec (fun _ => 0) (by simp)
  rw [E_const π21_mem, stratValue_eq_E] at this
  norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, π21, O1] at this

/-- **Target 20 (Fact 2.1), `π ∉ convexHull C_π`**, directly by the separating option `O_1`: the
half-space `{ρ : E_ρ(O_1) ≥ 0}` is convex and contains every candidate but not `π`.
Source: [[Deference Done Better]] §2 l. 206 ("the purple line … `E_ρ(O_1) = 0`"), fn 32
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_not_mem_hull : π21 ∉ convexHull ℝ (↑(fact21.cands π21) : Set (Fin 3 → ℝ)) := by
  intro hmem
  obtain ⟨h0, h1, h2⟩ := fact21_P
  have hconv : Convex ℝ {ρ : Fin 3 → ℝ | 0 ≤ E ρ O1} :=
    convex_halfSpace_ge ⟨fun a b => E_add_left a b O1, fun c a => E_smul_left c a O1⟩ _
  have hsub : (↑(fact21.cands π21) : Set (Fin 3 → ℝ)) ⊆ {ρ : Fin 3 → ℝ | 0 ≤ E ρ O1} := by
    intro y hy
    rw [mem_coe, Frame.mem_cands] at hy
    obtain ⟨w, _, rfl⟩ := hy
    fin_cases w <;> norm_num [Set.mem_setOf_eq, E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, O1]
  have := convexHull_min hsub hconv hmem
  rw [Set.mem_setOf_eq, fact21_E_O1.2.2.2] at this
  norm_num at this

/-! ## Figure 5's `F₂` and fn 52 (findings F3) -/

/-- Figure 5's `F₂`: rows `(2/4, 1/4, 1/4)`, `(6/16, 8/16, 2/16)`, `(1/4, 1/4, 2/4)`.
Source: [[Deference Done Better]] §4 l. 316 (Figure 5)
Kind: D
Fidelity: exact -/
def fig5F2 : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 4, 1 / 4] ![3 / 8, 1 / 2, 1 / 8] ![1 / 4, 1 / 4, 1 / 2]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `F₂`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F2_P : fig5F2.P 0 = ![1 / 2, 1 / 4, 1 / 4] ∧ fig5F2.P 1 = ![3 / 8, 1 / 2, 1 / 8] ∧
    fig5F2.P 2 = ![1 / 4, 1 / 4, 1 / 2] :=
  ⟨rfl, rfl, rfl⟩

/-- Fn 52's variable `X = (5, −1, −10)`.
Source: [[Deference Done Better]] fn 52 l. 1209
Kind: D
Fidelity: exact -/
def X52 : Fin 3 → ℝ := ![5, -1, -10]

/-- The uniform deferrer on three worlds (Figure 5's `π`).
Source: [[Deference Done Better]] §4 l. 313
Kind: D
Fidelity: exact -/
def π5 : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- On `F₂`, `E_{P_1}(X) = −1/4`, `E_{P_2}(X) = 1/8`, `E_{P_3}(X) = −4`: the cut `{E(X) ≥ 0}`
contains `P_2` alone. (Fn 52 refers to this frame, not to Fact 2.1's — findings F3.)
Source: [[Deference Done Better]] fn 52, §4 l. 321
Kind: L
Fidelity: exact -/
theorem fig5F2_E_X52 :
    E (fig5F2.P 0) X52 = -1 / 4 ∧ E (fig5F2.P 1) X52 = 1 / 8 ∧ E (fig5F2.P 2) X52 = -4 := by
  obtain ⟨h0, h1, h2⟩ := fig5F2_P
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, X52]

/-- **Fn 52 verified.** On `F₂` with the uniform `π`, Total Trust fails at `(X, 0)`:
`[E(X) ≥ 0] = {w_2}` and the product sum is `π(w_2) · X(w_2) = −1/3 < 0`.
Source: [[Deference Done Better]] fn 52, §4 l. 321
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig5F2_not_totalTrust : ¬ TotalTrust π5 fig5F2 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fig5F2_P
  have hsum := h.event_sum X52 0
  have hev : fig5F2.estEvent X52 0 = {1} := by
    ext w
    fin_cases w <;> norm_num [Frame.mem_estEvent, Fin.ext_iff, E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, X52]
  rw [hev] at hsum
  norm_num [π5, X52] at hsum

/-- `F₂`'s other rows are distinct from `P_2` (the middle row).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F2_ne : fig5F2.P 0 ≠ fig5F2.P 1 ∧ fig5F2.P 2 ≠ fig5F2.P 1 := by
  obtain ⟨h0, h1, h2⟩ := fig5F2_P
  constructor
  · intro h; have := congrFun h 0; rw [h0, h1] at this; norm_num at this
  · intro h; have := congrFun h 0; rw [h2, h1] at this; norm_num at this

/-- `P_2`'s cell in `F₂` is `{w_2}`, and its self-mass is `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fig5F2_cell : fig5F2.cell (fig5F2.P 1) = {1} ∧ fig5F2.selfMass (fig5F2.P 1) = 1 / 2 := by
  obtain ⟨hne01, hne21⟩ := fig5F2_ne
  have hc : fig5F2.cell (fig5F2.P 1) = {1} := by
    ext w; fin_cases w <;> simp [Frame.mem_cell, hne01, hne21]
  refine ⟨hc, ?_⟩
  rw [Frame.selfMass, hc]
  norm_num [mass, fig5F2_P.2.1]

/-- **Figure 5's `F₂`, `P_2` is not modestly informed**, witnessed by fn 52's cut: `P̂_2 = w_2`,
the other candidates and `P̂_2` all have `E(X) ≤ 0`, but `E_{P_2}(X) = 1/8 > 0`. A three-world
failure of the modest-informedness half of Theorem 7.6's fourth condition.
Source: [[Deference Done Better]] §4 l. 321–323, fn 52
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig5F2_not_modestlyInformed : ¬ fig5F2.ModestlyInformed (fig5F2.P 1) := by
  rintro ⟨_, hmem⟩
  obtain ⟨hne01, hne21⟩ := fig5F2_ne
  obtain ⟨h0, h1, h2⟩ := fig5F2_P
  obtain ⟨_, hsm⟩ := fig5F2_cell
  have hinf : E (fig5F2.informed (fig5F2.P 1)) X52 = -1 := by
    simp only [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, Frame.informed, hsm]
    simp only [hne01, hne21, if_false, if_true]
    norm_num [h1, X52]
  have hconv : Convex ℝ {ρ : Fin 3 → ℝ | E ρ X52 ≤ 0} :=
    convex_halfSpace_le ⟨fun a b => E_add_left a b X52, fun c a => E_smul_left c a X52⟩ _
  have hsub : insert (fig5F2.informed (fig5F2.P 1)) (↑(fig5F2.candsMinus (fig5F2.P 1)) : Set (Fin 3 → ℝ)) ⊆
      {ρ : Fin 3 → ℝ | E ρ X52 ≤ 0} := by
    intro y hy
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · rw [Set.mem_setOf_eq, hinf]; norm_num
    · rw [mem_coe, Frame.mem_candsMinus, Frame.mem_cands] at hy
      obtain ⟨hne, w, _, rfl⟩ := hy
      fin_cases w
      · norm_num [Set.mem_setOf_eq, E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, X52]
      · exact absurd rfl hne
      · norm_num [Set.mem_setOf_eq, E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h2, X52]
  have := convexHull_min hsub hconv hmem
  rw [Set.mem_setOf_eq, fig5F2_E_X52.2.1] at this
  norm_num at this

end

end Cleanroom.Found.LitDdbFrames.Examples
