import Cleanroom.Corrigibility.LegitNegDynamic.Cells
import Cleanroom.Corrigibility.LegitNegPricing.Scoring
import Cleanroom.Corrigibility.LegitNegPricing.Timing

/-!
# D3: S2 referenced to the agent's actual information — declining a free consultation

Package `legit-neg-dynamic`, target 4. Sources: `clusters/D/NEGATIVES.md` D3 (i)–(iii);
`clusters/D/VERIFY.md` "D3 — narrowed" (V3); `clusters/D/fixtures/d3_s2_reference_info.py`,
`verify_D.py` V3; pinned by [[corr-legit-neg-inventory]] item 048.

"Not consulting" is cdot under static's prior-referenced `P.S2` (`P1 (S2) a = P(L | a) · H a`,
pricing's `P1_S2_eq`); "consulting" is the finest partition, where the state-referenced score is
`u` itself (`P1_S2cell_singleton_eq`), so the consulting value is `∑ s, π s · max_a [leg s a] u s a`.
The score vector depends on what the agent chose to learn, which is why target 2 does not apply
and the value of the free consultation can be negative. General results: with `u = 0` on void
terminals the VOI is non-negative (D3(ii)); V3's exact condition — a strict negative-VOI instance
has a void world the humans rate above the state's best legitimate option
(`exists_void_above_of_consultVOI_neg`); and the harm is to eagerness-to-learn and `P(L)` only:
the humans' graded EU `H` prefers the uninformed choice (D3(iii)). The escape (the negligence
reference `S1 u`) restores non-negative VOI. No `Hcond` junk anywhere: `S2` reads the prior.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A]

/-- The state's best legitimate value, `max_a [leg s a] · u s a` (the informed T2 cdot value at the
fully revealing cell `{s}` under the state-referenced score `u`).
Source: [[corr-legit-neg-inventory]] item 048 (D3, "consulting")
Kind: D
Fidelity: exact -/
noncomputable def maxLeg (P : Problem S A) (s : S) : ℚ :=
  univ.sup' univ_nonempty fun a => ind (P.leg s a) * P.u s a

/-- **The consulting value**: `∑ s, π s · max_a [leg s a] · u s a` — learn the state for free, then
act on the S2 score referenced to the state (`d3_s2_reference_info.py:33-40`).
Source: [[corr-legit-neg-inventory]] item 048 (D3)
Kind: D
Fidelity: exact -/
noncomputable def consultValue (P : Problem S A) : ℚ := ∑ s, P.prior s * maxLeg P s

/-- **The uninformed value**: the best cdot value under `P.S2` (the bet referenced to the prior,
the agent's actual issuance-time information when it does not consult).
Source: [[corr-legit-neg-inventory]] item 048 (D3)
Kind: D
Fidelity: exact -/
noncomputable def uninformedValue (P : Problem S A) : ℚ := univ.sup' univ_nonempty (P.P1 P.S2)

/-- **The value of the free consultation** by the agent's own objective, `consultValue −
uninformedValue`.
Source: [[corr-legit-neg-inventory]] item 048 (D3)
Kind: D
Fidelity: exact -/
noncomputable def consultVOI (P : Problem S A) : ℚ := consultValue P - uninformedValue P

/-- `le_maxLeg`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_maxLeg (P : Problem S A) (s : S) (a : A) : ind (P.leg s a) * P.u s a ≤ maxLeg P s :=
  Finset.le_sup' (fun a => ind (P.leg s a) * P.u s a) (mem_univ a)

/-- The consulting value is the T1 cdot value, under the state-referenced score `S2cell (fun s =>
{s})`, of any policy that maximises the informed score in every state (positive priors, so the
singleton cells are the finest partition of record).
Source: [[corr-legit-neg-inventory]] item 048; pricing `P1_S2cell_singleton_eq`
Kind: L
Fidelity: exact -/
theorem consultValue_eq_policyValue [DecidableEq S] (P : Problem S A) (hprior : ∀ s, 0 < P.prior s)
    (π : S → A) (hπ : ∀ s a, ind (P.leg s a) * P.u s a ≤ ind (P.leg s (π s)) * P.u s (π s)) :
    consultValue P = policyValue P (P.S2cell fun s => {s}) π := by
  unfold consultValue policyValue
  refine Finset.sum_congr rfl fun s _ => ?_
  have hmax : maxLeg P s = ind (P.leg s (π s)) * P.u s (π s) :=
    le_antisymm (Finset.sup'_le _ _ fun a _ => hπ s a) (le_maxLeg P s (π s))
  have hS2 : P.S2cell (fun s => {s}) s (π s) (π s) = P.u s (π s) := by
    unfold Problem.S2cell Problem.Hc
    rw [Finset.sum_eq_single s]
    · rw [P.cellprior_singleton s (hprior s) s, if_pos rfl, one_mul]
    · intro t _ hts; rw [P.cellprior_singleton s (hprior s) t, if_neg hts, zero_mul]
    · intro h; exact absurd (mem_univ s) h
  rw [hmax, hS2]; ring

/-! ### D3(i): the toy -/

/-- **D3's toy** (`d3_s2_reference_info.py:24-27`): states `g = 0`, `b = 1` (prior `1/2` each);
`a_x = 0` voids in `g`, where the humans' graded quality is `q = 1`, and keeps legitimacy in `b`
with `q = 2/5`; `a_y = 1` keeps legitimacy in both with `q = 1/5`.
Source: [[corr-legit-neg-inventory]] item 048 (D3(i))
Kind: D
Fidelity: exact -/
def d3Toy : Problem (Fin 2) (Fin 2) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp [Fin.sum_univ_two]; try norm_num
  leg := fun s a => !(decide (s = 0) && decide (a = 0))
  u := fun s a => ![![1, 1/5], ![2/5, 1/5]] s a

/-- `d3Toy_maxLeg`: supporting lemma (no headline): `maxLeg = (1/5, 2/5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d3Toy_maxLeg : maxLeg d3Toy 0 = 1/5 ∧ maxLeg d3Toy 1 = 2/5 := by
  unfold maxLeg
  rw [sup'_fin2, sup'_fin2]
  simp [d3Toy]; try norm_num

/-- **D3(i), the numbers**: not consulting, `cdot-S2 (a_x) = 7/20 > 1/5 = cdot-S2 (a_y)`;
consulting is worth `3/10`; the free consultation is worth `−1/20` by the agent's own objective,
and `P(L)` is `1/2` for the uninformed choice against `1` for the consulting policy.
Source: [[corr-legit-neg-inventory]] item 048 (D3(i)); `d3_s2_reference_info.py:41-56`
Kind: N+
Fidelity: exact -/
theorem d3Toy_numbers :
    d3Toy.P1 d3Toy.S2 0 = 7/20 ∧ d3Toy.P1 d3Toy.S2 1 = 1/5 ∧ uninformedValue d3Toy = 7/20 ∧
    consultValue d3Toy = 3/10 ∧ consultVOI d3Toy = -1/20 ∧
    d3Toy.PL 0 = 1/2 ∧ policyPL d3Toy ![1, 0] = 1 := by
  have hPL0 : d3Toy.PL 0 = 1/2 := by simp [d3Toy, Problem.PL, Problem.mass, Fin.sum_univ_two]; try norm_num
  have hPL1 : d3Toy.PL 1 = 1 := by simp [d3Toy, Problem.PL, Problem.mass, Fin.sum_univ_two]; try norm_num
  have hH0 : d3Toy.H 0 = 7/10 := by simp [d3Toy, Problem.H, Problem.W, EU, Fin.sum_univ_two]; try norm_num
  have hH1 : d3Toy.H 1 = 1/5 := by simp [d3Toy, Problem.H, Problem.W, EU, Fin.sum_univ_two]; try norm_num
  have h0 : d3Toy.P1 d3Toy.S2 0 = 7/20 := by rw [P1_S2_eq, hPL0, hH0]; try norm_num
  have h1 : d3Toy.P1 d3Toy.S2 1 = 1/5 := by rw [P1_S2_eq, hPL1, hH1]; try norm_num
  have hun : uninformedValue d3Toy = 7/20 := by
    unfold uninformedValue; rw [sup'_fin2, h0, h1]; try norm_num
  have hcons : consultValue d3Toy = 3/10 := by
    unfold consultValue
    rw [Fin.sum_univ_two, d3Toy_maxLeg.1, d3Toy_maxLeg.2]
    simp [d3Toy]; try norm_num
  refine ⟨h0, h1, hun, hcons, ?_, hPL0, ?_⟩
  · unfold consultVOI; rw [hun, hcons]; try norm_num
  · simp [policyPL, d3Toy, Fin.sum_univ_two]; try norm_num

/-- **D3(iii) on the toy: the humans' graded EU prefers the uninformed choice** — `H a_x = 7/10`
against the consulting policy's `3/10`.
Source: [[corr-legit-neg-inventory]] item 048 (D3(iii)); `d3_s2_reference_info.py:57-61`
Kind: N+
Fidelity: exact -/
theorem d3Toy_H_prefers_uninformed :
    d3Toy.H 0 = 7/10 ∧ policyEU d3Toy d3Toy.u ![1, 0] = 3/10 := by
  constructor
  · simp [d3Toy, Problem.H, Problem.W, EU, Fin.sum_univ_two]; try norm_num
  · simp [policyEU, d3Toy, Fin.sum_univ_two]; try norm_num

/-- **The escape on the toy**: with the negligence reference `S1 u` (scores fixed per terminal,
whatever the agent learned) the uninformed values are `(1/5, 1/5)` and the consultation is worth
`+1/10`.
Source: [[corr-legit-neg-inventory]] item 048 (D3 escape); `d3_s2_reference_info.py:63-67`
Kind: N+
Fidelity: exact -/
theorem d3Toy_escape :
    d3Toy.P1 (S1 d3Toy.u) 0 = 1/5 ∧ d3Toy.P1 (S1 d3Toy.u) 1 = 1/5 ∧
    consultValue d3Toy - univ.sup' univ_nonempty (d3Toy.P1 (S1 d3Toy.u)) = 1/10 := by
  have h0 : d3Toy.P1 (S1 d3Toy.u) 0 = 1/5 := by simp [d3Toy, Problem.P1, S1, Fin.sum_univ_two]; try norm_num
  have h1 : d3Toy.P1 (S1 d3Toy.u) 1 = 1/5 := by simp [d3Toy, Problem.P1, S1, Fin.sum_univ_two]; try norm_num
  refine ⟨h0, h1, ?_⟩
  rw [sup'_fin2, h0, h1, d3Toy_numbers.2.2.2.1]; try norm_num

/-! ### The general results -/

/-- `H` is bounded by the consulting value whenever `u ≥ 0` and every void terminal of `a` is
rated no higher than the state's best legitimate value (V3's condition).
Source: VERIFY D "D3 — narrowed" (V3)
Kind: L
Fidelity: exact -/
lemma H_le_consultValue_of_cond (P : Problem S A) (a : A)
    (hcond : ∀ s, P.leg s a = false → P.u s a ≤ maxLeg P s) : P.H a ≤ consultValue P := by
  unfold Problem.H Problem.W EU consultValue
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (P.prior_nonneg s)
  by_cases hl : P.leg s a = true
  · have := le_maxLeg P s a; rwa [hl, ind_true, one_mul] at this
  · simp [Bool.not_eq_true] at hl; exact hcond s hl

/-- **V3's exact condition (the headline of D3, narrowed)**: with `0 ≤ u`, if every state where
`a` voids has `u s a ≤ max_b [leg s b] u s b`, then `a`'s uninformed value `P(L | a) · H a` is at
most the consulting value.
Source: VERIFY D "D3 — narrowed" (V3); [[corr-legit-neg-inventory]] item 048
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ u` (the sources' range), V3's condition at `a` -/
theorem uninformed_le_consultValue_of_cond (P : Problem S A) (hu : ∀ s a, 0 ≤ P.u s a) (a : A)
    (hcond : ∀ s, P.leg s a = false → P.u s a ≤ maxLeg P s) :
    P.P1 P.S2 a ≤ consultValue P := by
  rw [P1_S2_eq]
  have hH : 0 ≤ P.H a := Finset.sum_nonneg fun s _ => mul_nonneg (P.prior_nonneg s) (hu s a)
  calc P.PL a * P.H a ≤ 1 * P.H a := mul_le_mul_of_nonneg_right (P.mass_le_one _) hH
    _ = P.H a := one_mul _
    _ ≤ consultValue P := H_le_consultValue_of_cond P a hcond

/-- **D3(ii): with zero void quality the consultation is never declined**: `0 ≤ u` and `u = 0` on
every void terminal give `0 ≤ consultVOI`.
Source: [[corr-legit-neg-inventory]] item 048 (D3(ii)); `d3_s2_reference_info.py:68-86`
Kind: C
Fidelity: exact
Hyps: (a) `0 ≤ u`; `u = 0` on void terminals -/
theorem consultVOI_nonneg_of_void_zero (P : Problem S A) (hu : ∀ s a, 0 ≤ P.u s a)
    (hz : ∀ s a, P.leg s a = false → P.u s a = 0) : 0 ≤ consultVOI P := by
  unfold consultVOI uninformedValue
  have : univ.sup' univ_nonempty (P.P1 P.S2) ≤ consultValue P :=
    Finset.sup'_le _ _ fun a _ => uninformed_le_consultValue_of_cond P hu a fun s hs => by
      rw [hz s a hs]
      exact le_trans (by simp [hz s a hs]) (le_maxLeg P s a)
  linarith

/-- **D3, the contrapositive (V3)**: a strict negative-VOI instance (with `0 ≤ u`) has an uninformed
maximiser `a` and a state `s` where `a` voids and the humans rate the void world strictly above
the state's best legitimate option, `maxLeg P s < u s a`. So D3 bites only when the humans' graded
`q` ranks some void world above every legitimate alternative in the same state — never under a
lexical ordering of world quality, never with the floor inside the humans' bet.
Source: VERIFY D "D3 — narrowed" (V3); [[corr-legit-neg-inventory]] item 048
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ u`, `consultVOI < 0` -/
theorem exists_void_above_of_consultVOI_neg (P : Problem S A) (hu : ∀ s a, 0 ≤ P.u s a)
    (hneg : consultVOI P < 0) :
    ∃ a, (∀ b, P.P1 P.S2 b ≤ P.P1 P.S2 a) ∧ ∃ s, P.leg s a = false ∧ maxLeg P s < P.u s a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (P.P1 P.S2)
  refine ⟨a, fun b => ha ▸ Finset.le_sup' (P.P1 P.S2) (mem_univ b), ?_⟩
  by_contra hno
  push Not at hno
  have := uninformed_le_consultValue_of_cond P hu a fun s hs => hno s hs
  unfold consultVOI uninformedValue at hneg
  rw [ha] at hneg
  linarith

/-- A strict maximiser of `[leg] · u` in a state is legitimate when `0 ≤ u` and some other option
exists (a void option scores `0`, which cannot strictly beat a non-negative value).
Source: [[corr-legit-neg-inventory]] item 048 (D3(iii) proof)
Kind: L
Fidelity: exact -/
lemma leg_of_strict_max (P : Problem S A) (hu : ∀ s a, 0 ≤ P.u s a) (s : S) (a : A)
    (hstrict : ∀ b, b ≠ a → ind (P.leg s b) * P.u s b < ind (P.leg s a) * P.u s a)
    (hother : ∃ b, b ≠ a) : P.leg s a = true := by
  obtain ⟨b, hb⟩ := hother
  by_contra hl
  simp [Bool.not_eq_true] at hl
  have h := hstrict b hb
  rw [hl, ind_false, zero_mul] at h
  have : 0 ≤ ind (P.leg s b) * P.u s b := mul_nonneg (ind_nonneg _) (hu s b)
  linarith

/-- **D3(iii): the harm is to eagerness-to-learn and `P(L)`, not to the humans' graded value.**
If the consultation is strictly declined (`consultVOI < 0`, `0 ≤ u`) and the informed maximiser
`π` is strict in every state (with at least two options), then `π` is legitimate everywhere and the
humans' graded EU prefers the uninformed maximiser: `policyEU P u π < H a*`. Ignorance partly
undoes the floor's distortion.
Source: [[corr-legit-neg-inventory]] item 048 (D3(iii)); `d3_s2_reference_info.py:57-61`, grid
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ u`; strictness of the informed maximiser; a second option; `consultVOI < 0` -/
theorem H_prefers_uninformed_of_consultVOI_neg (P : Problem S A) (hu : ∀ s a, 0 ≤ P.u s a)
    (π : S → A)
    (hstrict : ∀ s b, b ≠ π s → ind (P.leg s b) * P.u s b < ind (P.leg s (π s)) * P.u s (π s))
    (hother : ∀ s, ∃ b, b ≠ π s) (astar : A) (hmax : P.P1 P.S2 astar = uninformedValue P)
    (hneg : consultVOI P < 0) :
    (∀ s, P.leg s (π s) = true) ∧ policyEU P P.u π < P.H astar := by
  have hleg : ∀ s, P.leg s (π s) = true := fun s =>
    leg_of_strict_max P hu s (π s) (hstrict s) (hother s)
  refine ⟨hleg, ?_⟩
  have hcons : consultValue P = policyEU P P.u π := by
    unfold consultValue policyEU
    refine Finset.sum_congr rfl fun s _ => ?_
    have hm : maxLeg P s = ind (P.leg s (π s)) * P.u s (π s) :=
      le_antisymm (Finset.sup'_le _ _ fun b _ => by
        by_cases hb : b = π s
        · rw [hb]
        · exact (hstrict s b hb).le) (le_maxLeg P s (π s))
    rw [hm, hleg s, ind_true, one_mul]
  have hH : 0 ≤ P.H astar := Finset.sum_nonneg fun s _ => mul_nonneg (P.prior_nonneg s) (hu s astar)
  have hPLH : P.PL astar * P.H astar ≤ P.H astar := by
    calc P.PL astar * P.H astar ≤ 1 * P.H astar :=
        mul_le_mul_of_nonneg_right (P.mass_le_one _) hH
      _ = P.H astar := one_mul _
  unfold consultVOI at hneg
  rw [← hmax, P1_S2_eq, hcons] at hneg
  linarith

/-- **The escape, in general**: under the negligence reference (`S1 u`, scores fixed per
terminal), the consulting value is at least every uninformed value, so the consultation is never
declined — target 2's Good's theorem at the finest partition, stated directly.
Source: [[corr-legit-neg-inventory]] item 048 (D3 escape, "D2(i) applies")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem consultValue_ge_uninformed_S1 (P : Problem S A) :
    univ.sup' univ_nonempty (P.P1 (S1 P.u)) ≤ consultValue P := by
  refine Finset.sup'_le _ _ fun a _ => ?_
  unfold Problem.P1 consultValue
  refine Finset.sum_le_sum fun s _ => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_maxLeg P s a) (P.prior_nonneg s)

end Cleanroom.Corrigibility.LegitNegDynamic
