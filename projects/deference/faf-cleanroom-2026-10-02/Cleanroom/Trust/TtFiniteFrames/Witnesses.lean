import Cleanroom.Trust.TtFiniteFrames.Chains
import Cleanroom.Trust.TtFiniteFrames.SoftCollapse
import Cleanroom.Trust.TtFiniteFrames.Weatherson
import Cleanroom.Trust.TtFiniteFrames.Squares

/-!
# Witnesses for the headlines (repair rounds 1 and 2)

**Round 1.** Audit r1 (both lenses) found that `softCM_immodest` (I2) and `mutual_cmToward_eq`
(I3, R1) shipped no inhabitant of their full hypothesis packages. This file supplies them from the
package's own `T4.FA` — the uniform prior's partition expert on `{{0,1},{2}}`, a non-omniscient
immodest frame: every partition expert satisfies the soft identity for *every* indicator family
(no ramp shape needed), and every immodest frame conditionally-martingales toward itself.
Every inhabitant of either package is immodest on the support — that is what the theorems say —
and (round 2, `softCM_iff_condMartingaleAt_all`) every inhabitant of I2's `hsoft` is a
conditional martingale at every world, so for a full-support prior the inhabitants are exactly
T1's partition experts and `T4.FA` is the generic one. The value of the witnesses is that the
packages are consistent and inhabited by a non-degenerate frame.

**Round 2.** `Lab042.converse_witness`: an inhabitant of `partition_coarse_converse`'s full
package (the reflexive `K₂ = {{0},{1},W}` does not refine the partitional anchor
`Q = {{0,2},{1},{0,2}}`), so the theorem yields a menu on which every `Q`-recommended strategy
strictly beats every `K₂`-recommended one under the uniform prior (audit r2 fidelity N5).
`Thm51Inhabitant.inhabitant`: the non-degenerate inhabitant of `thm51`'s hypothesis on `Fin 6`
that audit r1 (adversarial N6) asked for and audit r2 (adversarial N3, probe Q5) compiled —
`a X` is `𝔐`-measurable and non-constant, `c` does not refine `d`, and the composite `D.comp C`
is not immodest, so it is no partition expert and `thm51` there is not an instance of T1.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **N+ witness for I2's hypothesis package.** Every partition expert of a full-support prior
satisfies the soft identity for every `ρ` whatsoever (no ramp shape needed), every `X`, `t` and
`δ`: on a cell the estimate is constant, so the indicator is constant, and the cell sum of `π X`
equals the cell sum of `π E_w X` (`Frame.ofPartition_E`).
Source: none: audit r1 N1 (both lenses)
Kind: N+
Fidelity: n/a -/
theorem ofPartition_soft_identity {ι : Type} [DecidableEq ι] {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    (f : W → ι) (ρ : ℝ → ℝ → ℝ → ℝ) (X : W → ℝ) (t δ : ℝ) :
    ∑ w, π w * X w * ρ δ t (E ((Frame.ofPartition π hpos f).P w) X) =
      ∑ w, π w * E ((Frame.ofPartition π hpos f).P w) X *
        ρ δ t (E ((Frame.ofPartition π hpos f).P w) X) := by
  set F := Frame.ofPartition π hpos f with hF
  have hK := Corr.ofMap_partitional f
  rw [hK.sum_cells (fun w => π w * X w * ρ δ t (E (F.P w) X)),
    hK.sum_cells (fun w => π w * E (F.P w) X * ρ δ t (E (F.P w) X))]
  apply sum_congr rfl
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  have hrow : ∀ w ∈ Corr.ofMap f v, F.P w = F.P v := fun w hw =>
    (Frame.ofPartition_P_inj π hpos f w v).2 (Corr.mem_ofMap.1 hw)
  calc ∑ w ∈ Corr.ofMap f v, π w * X w * ρ δ t (E (F.P w) X)
      = ρ δ t (E (F.P v) X) * ∑ w ∈ Corr.ofMap f v, π w * X w := by
        rw [mul_sum]; apply sum_congr rfl; intro w hw; rw [hrow w hw]; ring
    _ = ρ δ t (E (F.P v) X) * (E (F.P v) X * mass π (Corr.ofMap f v)) := by
        rw [hF, Frame.ofPartition_E π hpos f v X]
    _ = ∑ w ∈ Corr.ofMap f v, π w * E (F.P w) X * ρ δ t (E (F.P w) X) := by
        rw [mass, mul_sum, mul_sum]; apply sum_congr rfl; intro w hw; rw [hrow w hw]; ring

/-- `softCM_immodest` on that inhabitant, for any ramp: T1's expert is immodest (as T1 already
says by another route) — the point is that the headline's package is inhabited.
Source: none: audit r1 N1
Kind: L
Fidelity: n/a -/
theorem softCM_immodest_ofPartition {ι : Type} [DecidableEq ι] {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) (f : W → ι) {ρ : ℝ → ℝ → ℝ → ℝ} (hρ : IsRamp ρ) :
    ∀ w, 0 < π w → (Frame.ofPartition π hpos f).selfMass ((Frame.ofPartition π hpos f).P w) = 1 :=
  softCM_immodest hρ (fun X t δ _ _ => ofPartition_soft_identity hpos f ρ X t δ)

namespace T4

/-- `A`'s expert is not omniscient: its row at `0` is `(1/2, 1/2, 0)`, not `δ₀`.
Source: none: audit r1 N1
Kind: N+
Fidelity: n/a -/
theorem FA_not_omniscient : FA.P 0 ≠ Pi.single 0 1 := by
  intro h
  have := congrFun h 1
  rw [FA, Frame.ofPartition_P_apply] at this
  simp [mass_ofMap_eq, Fin.sum_univ_three, πA, cA] at this

/-- **The witness for I2 and I3 (R1).** `T4.FA` (uniform prior on `Fin 3`, cells `{0,1},{2}`)
inhabits `softCM_immodest`'s package for every indicator family, is immodest (through
`softCM_immodest` at the hard indicator), satisfies mutual R1 with itself at every world, and is
not omniscient. Its row at `0`, `(1/2, 1/2, 0)`, is a genuine non-trivial estimate.
Source: none: audit r1 N1/N2 (both lenses)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem FA_witness :
    (∀ (ρ : ℝ → ℝ → ℝ → ℝ) (X : Fin 3 → ℝ) (t δ : ℝ),
        ∑ w, πA w * X w * ρ δ t (E (FA.P w) X) = ∑ w, πA w * E (FA.P w) X * ρ δ t (E (FA.P w) X)) ∧
      FA.Immodest ∧ (∀ w, CMToward FA FA w) ∧ FA.P 0 ≠ Pi.single 0 1 := by
  have himm : FA.Immodest := fun w =>
    softCM_immodest_ofPartition hposA cA isRamp_hardIndicator w (hposA w)
  exact ⟨fun ρ X t δ => ofPartition_soft_identity hposA cA ρ X t δ, himm,
    fun w => cmToward_self_of_immodest himm w, FA_not_omniscient⟩

end T4

/-! ## Round 2: the Geanakoplos converse on trust-lab-042's frame -/

namespace Lab042

/-- **N+ witness for `partition_coarse_converse`'s full package.** trust-lab-042's coarser
experiment `K₂ = {{0},{1},W}` is reflexive (indeed RTN) and does not refine the partitional
anchor `Q = {{0,2},{1},{0,2}}` (`K₂ 2 = W ⊄ {0,2}`), so under the uniform prior some menu makes
every `Q`-recommended strategy strictly more valuable than every `K₂`-recommended one. (On the
menu the proof builds at `w = 2` — `{0, (1, −3, 1)}` — the `Q`-agent earns `2/3` and the
`K₂`-agent `1/3`.) Together with `Lab042.values` (on the lab's own menu the anchor ties with the
finer `K₁` at `4/9`, and `K₂` earns `5/9`), this is the pair G3 / G3-converse on one frame.
Source: trust-lab-042; audit r2 fidelity N5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem converse_witness :
    ¬ Corr.Refines K₂ Q ∧
      ∃ 𝒪 : DecisionProblem (Fin 3), 𝒪.Nonempty ∧ ∀ S₁ S₂,
        F₂.Recommended 𝒪 S₁ → FQ.Recommended 𝒪 S₂ →
          stratValue unif3 S₁ < stratValue unif3 S₂ :=
  ⟨by decide,
    partition_coarse_converse unif3_pos structure_facts.2.1.1 structure_facts.2.2.1 (by decide)⟩

end Lab042

/-! ## Round 2: a non-degenerate inhabitant of Theorem 5.1's hypothesis -/

namespace Thm51Inhabitant

/-- The uniform prior on `Fin 6`.
Source: none: infrastructure (audit r1 adversarial N6, audit r2 adversarial N3 probe Q5)
Kind: D
Fidelity: n/a -/
def π6 : Fin 6 → ℝ := fun _ => 1 / 6

/-- Full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hpos6 : ∀ w, 0 < π6 w := fun _ => by norm_num [π6]

/-- `𝔐`: cells `{0,1}, {2}, {3}, {4,5}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def c6 : Fin 6 → Fin 4 := ![0, 0, 1, 2, 3, 3]

/-- `𝔄`: cells `{0,2}, {1,3}, {4}, {5}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def d6 : Fin 6 → Fin 4 := ![0, 1, 0, 1, 2, 3]

/-- `X = 𝟙_{4,5}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def X6 : Fin 6 → ℝ := ![0, 0, 0, 0, 1, 1]

/-- Future-H's frame on `c`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def C6 : Frame (Fin 6) := Frame.ofPartition π6 hpos6 c6

/-- A's information frame on `d`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def D6 : Frame (Fin 6) := Frame.ofPartition π6 hpos6 d6

/-- `m X = (0,0,0,0,1,1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem m_val : condExp π6 hpos6 c6 X6 = ![0, 0, 0, 0, 1, 1] := by
  funext v
  unfold condExp
  rw [Frame.ofPartition_E_eq']
  fin_cases v <;> simp [Fin.sum_univ_six, π6, c6, X6]

/-- `a X = (0,0,0,0,1,1)`: `d`'s cells `{4}`, `{5}` are singletons, so `a` agrees with `m` there
for every `X`, and `m` vanishes on `{0,1,2,3}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a_val : condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) = ![0, 0, 0, 0, 1, 1] := by
  rw [m_val]
  funext v
  unfold condExp
  rw [Frame.ofPartition_E_eq']
  fin_cases v <;> simp [Fin.sum_univ_six, π6, d6]

/-- `a X` is `c`-measurable: `thm51`'s hypothesis holds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hmeas : ∀ v v', c6 v = c6 v' →
    condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) v =
      condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) v' := by
  intro v v' h
  rw [a_val]
  fin_cases v <;> fin_cases v' <;> first | rfl | (exact absurd h (by decide))

/-- **N+ inhabitant of `thm51`'s hypothesis package, beyond T1.** `a X = (0,0,0,0,1,1)` is not
constant; `c` does not refine `d`; and the composite `D.comp C` is not immodest at `0` (its row
there weights world `1` with `1/4`, yet differs from row `1` at world `2`: `1/2` vs `0`), so it is
no partition expert of any prior and `thm51` here is not an instance of T1
(`comp_ofPartition_eq_of_refines` does not apply). `thm51`'s conclusion holds for every
threshold. In the language of F-S1: `a X` is measurable for both `c` and `d`, hence constant on
the cells of their meet, and A's quote of this `X` coincides with the meet expert's — even though
the frame `D.comp C` is not that expert.
Source: [[route-transitivity]] §5.1; audit r1 adversarial N6, audit r2 adversarial N3 (probe Q5,
moved into the library)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem inhabitant :
    condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) 0 ≠
        condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) 4 ∧
      ¬ Blackwell.Refines c6 d6 ∧
      (0 < (Frame.comp D6 C6).P 0 1 ∧ (Frame.comp D6 C6).P 0 ≠ (Frame.comp D6 C6).P 1) ∧
      ¬ (Frame.comp D6 C6).Immodest ∧
      ∀ t : ℝ, t * mass π6 (univ.filter (fun w =>
          t ≤ condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) w)) ≤
        ∑ w ∈ univ.filter (fun w => t ≤ condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) w),
          π6 w * X6 w := by
  have hrows : 0 < (Frame.comp D6 C6).P 0 1 ∧ (Frame.comp D6 C6).P 0 ≠ (Frame.comp D6 C6).P 1 := by
    constructor
    · simp [Frame.comp, D6, C6, Frame.ofPartition_P_apply, mass_ofMap_eq, Fin.sum_univ_six,
        π6, c6, d6]
    · intro h
      have := congrFun h 2
      simp [Frame.comp, D6, C6, Frame.ofPartition_P_apply, mass_ofMap_eq, Fin.sum_univ_six,
        π6, c6, d6] at this
  refine ⟨by rw [a_val]; simp, ?_, hrows, ?_, thm51 π6 hpos6 c6 d6 X6 hmeas⟩
  · rintro ⟨g, hg⟩
    have h0 : d6 0 = g (c6 0) := congrFun hg 0
    have h1 : d6 1 = g (c6 1) := congrFun hg 1
    have hc : c6 0 = c6 1 := by decide
    rw [hc] at h0
    rw [← h0] at h1
    exact absurd h1 (by decide)
  · intro h
    obtain ⟨hpos, hne⟩ := hrows
    have h0 := h 0
    unfold Frame.selfMass mass at h0
    have hlt : ∑ v ∈ (Frame.comp D6 C6).cell ((Frame.comp D6 C6).P 0), (Frame.comp D6 C6).P 0 v <
        ∑ v, (Frame.comp D6 C6).P 0 v :=
      sum_lt_sum_of_subset (subset_univ _) (mem_univ 1)
        (fun hm => hne (Frame.mem_cell.1 hm).symm) hpos
        (fun j _ _ => (Frame.comp D6 C6).P_nonneg 0 j)
    rw [h0, (Frame.comp D6 C6).P_sum 0] at hlt
    exact lt_irrefl _ hlt

/-- The join of `c` and `d`: cells `{0,1,2,3}, {4,5}` (the components of the overlap graph of
`{{0,1},{2},{3},{4,5}}` and `{{0,2},{1,3},{4},{5}}`).
Source: none: infrastructure (audit r2 adversarial N3(b))
Kind: D
Fidelity: n/a -/
def e6 : Fin 6 → Fin 2 := ![0, 0, 0, 0, 1, 1]

/-- **On the inhabitant, A's quote is the join expert's quote.** `c` and `d` both refine the join
`e = {{0,1,2,3},{4,5}}`, `a X` is constant on its cells, so `a X = E[X ∣ e]`
(`quote_eq_condExp_of_common_coarsening`) and `thm51` there is T1 for `e`
(`thm51_of_common_coarsening`) — although `D.comp C` is not `e`'s partition expert, nor any
partition expert (`inhabitant`).
Source: [[route-transitivity]] §5.1; audit r2 adversarial N3(b)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem quote_eq_join :
    Blackwell.Refines c6 e6 ∧ Blackwell.Refines d6 e6 ∧
      condExp π6 hpos6 d6 (condExp π6 hpos6 c6 X6) = condExp π6 hpos6 e6 X6 := by
  have hce : Blackwell.Refines c6 e6 := ⟨![0, 0, 0, 1], by decide⟩
  have hde : Blackwell.Refines d6 e6 := ⟨![0, 0, 1, 1], by decide⟩
  refine ⟨hce, hde, quote_eq_condExp_of_common_coarsening π6 hpos6 hce hde X6 ?_⟩
  intro v v' h
  rw [a_val]
  fin_cases v <;> fin_cases v' <;> first | rfl | (exact absurd h (by decide))

end Thm51Inhabitant

end

end Cleanroom.Trust.TtFiniteFrames
