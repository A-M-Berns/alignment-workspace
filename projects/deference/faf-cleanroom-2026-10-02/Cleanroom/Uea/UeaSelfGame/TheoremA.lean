import Cleanroom.Uea.UeaSelfGame.Static
import Cleanroom.Uea.UeaSelfGame.FinSums

/-!
# Theorem A: the proposed theorem refuted, uniformly in `δ`

For every `δ ∈ (0,1)` the two-situation, two-action instance `U(aa) = 1`, `U(ab) = U(ba) = 0`,
`U(bb) = 1 − η` with `η := δ/(2(2−δ))`, `π* = aa` (the unique maximizer), `Po = ½ δ_{ab} + ½ δ_{bb}`,
under the static belief `μ = (1-δ) δ_{π*} + δ Po`: every action is available at both situations (so the
witness is convention-free), the Herrmann argmax is strict at both, the unique realized policy is `ba`
with `U(ba) = 0` (loss `= U* = 1`), and the trust bound holds at both situations. The conditionals are
rational functions of `δ`: `cond(s₀, a) = (1-δ)/(1-δ/2) < 1-η = cond(s₀, b)`, `cond(s₁, a) = 1 > (1-η)/2 =
cond(s₁, b)`.

This refutes [[summer-research-plan-2026--research-ideas-may-2026]] line 48, *"if a UDT1.0 agent
(1−δ)-believes that its policy is UDT1.1, then it is ε-optimal"*, read as: pointwise EDT conditional on
one's own action, static belief, `ε → 0` as `δ → 0` uniformly over instances (ATTRIBUTION-UNVETTED: the
note's §1 formalization of "believes"). Surviving neighbours: Theorem B (`Static.lean`) and Theorem C
(`Repaired.lean`). It also refutes the founding sketch's "two situations cannot do this", Idea 2's `O(δ)`
clause, Idea 7's `δ`-interpolation clause and the earlier lab's Prop 2★ (same witness).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static belief; not
rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

namespace TheoremA

open Finset

/-- `η(δ) := δ/(2(2−δ))`, the gap of the deviation's supporter `bb` below `U* = 1`.
Source: [[updateless-self-game]] §2 (Theorem A proof)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def η (δ : ℝ) : ℝ := δ / (2 * (2 - δ))
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem η_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 0 < η δ := by
  unfold η; apply div_pos h0; linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem η_lt_half {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : η δ < 1 / 2 := by
  unfold η; rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem η_le_δ {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : η δ ≤ δ := by
  unfold η; rw [div_le_iff₀ (by linarith)]; nlinarith

/-- The utility table: `U(aa) = 1`, `U(ab) = U(ba) = 0`, `U(bb) = 1 − η` (`a = 0`, `b = 1`).
Source: [[updateless-self-game]] §2 (Theorem A proof)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Ufun (δ : ℝ) (π : Fin 2 → Fin 2) : ℝ :=
  if π 0 = 0 then (if π 1 = 0 then 1 else 0) else (if π 1 = 0 then 0 else 1 - η δ)

/-- `Po = ½ δ_{ab} + ½ δ_{bb}`.
Source: [[updateless-self-game]] §2 (Theorem A proof)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Pofun (π : Fin 2 → Fin 2) : ℝ :=
  if π 0 = 0 then (if π 1 = 0 then 0 else 1 / 2) else (if π 1 = 0 then 0 else 1 / 2)

/-- The Theorem A instance at a given `δ ∈ (0,1)`.
Source: [[updateless-self-game]] §2 (Theorem A)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) : Game (Fin 2) (Fin 2) where
  U := Ufun δ
  U_nonneg := by
    intro π; unfold Ufun; have := η_lt_half h0 h1; split_ifs <;> linarith
  U_le_one := by
    intro π; unfold Ufun; have := η_pos h0 h1; split_ifs <;> linarith
  piStar := ![0, 0]
  piStar_max := by
    intro π
    simp only [Ufun, Matrix.cons_val_zero, Matrix.cons_val_one]
    have := η_pos h0 h1
    split_ifs <;> linarith
  Po := Pofun
  Po_mem := by
    refine ⟨fun π => ?_, ?_⟩
    · unfold Pofun; split_ifs <;> norm_num
    · rw [sum_fin2_arrow]
      simp [Fin.sum_univ_two, Pofun]
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_apply (π : Fin 2 → Fin 2) :
    (game δ h0 h1).mu π = (1 - δ) * (if π 0 = 0 ∧ π 1 = 0 then 1 else 0) + δ * Pofun π := by
  simp only [game, Game.mu, Game.muSelf]
  congr 2
  simp [funext_iff, Fin.forall_fin_two]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π : Fin 2 → Fin 2) : (game δ h0 h1).U π = Ufun δ π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem δ_eq : (game δ h0 h1).δ = δ := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem piStar_eq : (game δ h0 h1).piStar = ![0, 0] := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ustar_eq : (game δ h0 h1).Ustar = 1 := by
  simp [Game.Ustar, game, Ufun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem thr_eq : (game δ h0 h1).thr = 1 - δ := by
  simp [Game.thr, Ustar_eq, δ_eq]

/-! ### The four conditionals as rational functions of `δ` -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_00 : condDen (game δ h0 h1).mu 0 0 = 1 - δ / 2 := by
  unfold condDen; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, mu_apply, Pofun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_00 : (game δ h0 h1).condNum (game δ h0 h1).mu 0 0 = 1 - δ := by
  unfold Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, mu_apply, Pofun, U_apply, Ufun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_01 : condDen (game δ h0 h1).mu 0 1 = δ / 2 := by
  unfold condDen; rw [sum_fin2_arrow]
  simp [mu_apply, Pofun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_01 : (game δ h0 h1).condNum (game δ h0 h1).mu 0 1 = δ / 2 * (1 - η δ) := by
  unfold Game.condNum; rw [sum_fin2_arrow]
  simp [mu_apply, Pofun, U_apply, Ufun, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_10 : condDen (game δ h0 h1).mu 1 0 = 1 - δ := by
  unfold condDen; rw [sum_fin2_arrow]
  simp [mu_apply, Pofun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_10 : (game δ h0 h1).condNum (game δ h0 h1).mu 1 0 = 1 - δ := by
  unfold Game.condNum; rw [sum_fin2_arrow]
  simp [mu_apply, Pofun, U_apply, Ufun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_11 : condDen (game δ h0 h1).mu 1 1 = δ := by
  unfold condDen; rw [sum_fin2_arrow]
  simp [mu_apply, Pofun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_11 : (game δ h0 h1).condNum (game δ h0 h1).mu 1 1 = δ / 2 * (1 - η δ) := by
  unfold Game.condNum; rw [sum_fin2_arrow]
  simp [Fin.sum_univ_two, mu_apply, Pofun, U_apply, Ufun, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_00 : (game δ h0 h1).cond (game δ h0 h1).mu 0 0 = (1 - δ) / (1 - δ / 2) := by
  unfold Game.cond; rw [condNum_00, condDen_00]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_01 : (game δ h0 h1).cond (game δ h0 h1).mu 0 1 = 1 - η δ := by
  unfold Game.cond; rw [condNum_01, condDen_01]
  have : δ / 2 ≠ 0 := by positivity
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_10 : (game δ h0 h1).cond (game δ h0 h1).mu 1 0 = 1 := by
  unfold Game.cond; rw [condNum_10, condDen_10]
  have : 1 - δ ≠ 0 := by linarith
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_11 : (game δ h0 h1).cond (game δ h0 h1).mu 1 1 = (1 - η δ) / 2 := by
  unfold Game.cond; rw [condNum_11, condDen_11]
  have : δ ≠ 0 := ne_of_gt h0
  field_simp

/-- Every action is available at every situation: the witness is convention-free.
Source: [[updateless-self-game]] §2 ("Register … robust to the convention")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_all : ∀ s a : Fin 2, avail (game δ h0 h1).mu s a := by
  unfold avail
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [condDen_00]; linarith
  · rw [condDen_01]; linarith
  · rw [condDen_10]; linarith
  · rw [condDen_11]; linarith

/-- At `s₀`, `b` strictly beats `a`: `(1-δ)/(1-δ/2) < 1 − η` (the difference is exactly `η = δ/(2(2−δ))`; at `δ = 1/10`, `1/38`).
Source: [[updateless-self-game]] §2 (Theorem A proof, "At `s_0`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_00_lt_cond_01 :
    (game δ h0 h1).cond (game δ h0 h1).mu 0 0 < (game δ h0 h1).cond (game δ h0 h1).mu 0 1 := by
  rw [cond_00, cond_01]
  have h2 : 0 < 1 - δ / 2 := by linarith
  rw [div_lt_iff₀ h2]
  have h3 : 0 < 2 * (2 - δ) := by linarith
  have hη : η δ * (2 * (2 - δ)) = δ := div_mul_cancel₀ _ (ne_of_gt h3)
  nlinarith [hη]

/-- At `s₁`, `a` strictly beats `b`: `1 > (1 − η)/2`.
Source: [[updateless-self-game]] §2 (Theorem A proof, "At `s_1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_11_lt_cond_10 :
    (game δ h0 h1).cond (game δ h0 h1).mu 1 1 < (game δ h0 h1).cond (game δ h0 h1).mu 1 0 := by
  rw [cond_10, cond_11]
  have := η_pos h0 h1
  linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isArgmaxH_01 : (game δ h0 h1).IsArgmaxH (game δ h0 h1).mu 0 1 := by
  refine ⟨avail_all h0 h1 0 1, ?_⟩
  simp only [Fin.forall_fin_two]
  exact ⟨fun _ => (cond_00_lt_cond_01 h0 h1).le, fun _ => le_rfl⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isArgmaxH_10 : (game δ h0 h1).IsArgmaxH (game δ h0 h1).mu 1 0 := by
  refine ⟨avail_all h0 h1 1 0, ?_⟩
  simp only [Fin.forall_fin_two]
  exact ⟨fun _ => le_rfl, fun _ => (cond_11_lt_cond_10 h0 h1).le⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem argmax_0_eq : ∀ a : Fin 2, (game δ h0 h1).IsArgmaxH (game δ h0 h1).mu 0 a → a = 1 := by
  simp only [Fin.forall_fin_two]
  refine ⟨fun h => ?_, fun _ => trivial⟩
  exfalso
  have := h.2 1 (avail_all h0 h1 0 1)
  exact absurd (cond_00_lt_cond_01 h0 h1) (not_lt.2 this)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem argmax_1_eq : ∀ a : Fin 2, (game δ h0 h1).IsArgmaxH (game δ h0 h1).mu 1 a → a = 0 := by
  simp only [Fin.forall_fin_two]
  refine ⟨fun _ => trivial, fun h => ?_⟩
  exfalso
  have := h.2 0 (avail_all h0 h1 1 0)
  exact absurd (cond_11_lt_cond_10 h0 h1) (not_lt.2 this)

/-- The argmax is strict at both situations: `{b}` at `s₀`, `{a}` at `s₁`.
Source: [[updateless-self-game]] §2 (Theorem A, "the argmax is strict at both situations")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem strictArgmax : (game δ h0 h1).StrictArgmax (game δ h0 h1).mu := by
  unfold Game.StrictArgmax
  simp only [Fin.forall_fin_two]
  exact ⟨⟨1, isArgmaxH_01 h0 h1, fun a ha => argmax_0_eq h0 h1 a ha⟩,
    ⟨0, isArgmaxH_10 h0 h1, fun a ha => argmax_1_eq h0 h1 a ha⟩⟩

/-- The trust bound holds at both situations: `1 − η ≥ 1 − δ` at `s₀`, `1 ≥ 1 − δ` at `s₁`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §2 (Theorem A, "Trust bound")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_all : ∀ s : Fin 2, (game δ h0 h1).TB (game δ h0 h1).mu s := by
  simp only [Fin.forall_fin_two]
  constructor
  · refine ⟨1, avail_all h0 h1 0 1, ?_⟩
    rw [thr_eq, cond_01]; have := η_le_δ h0 h1; linarith
  · refine ⟨0, avail_all h0 h1 1 0, ?_⟩
    rw [thr_eq, cond_10]; linarith

/-- The unique realized policy is `ba`.
Source: [[updateless-self-game]] §2 (Theorem A, "Realized policy `(b,a)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem realizes_iff (π : Fin 2 → Fin 2) :
    (game δ h0 h1).Realizes (game δ h0 h1).mu π ↔ π = ![1, 0] := by
  constructor
  · intro h
    exact funext (Fin.forall_fin_two.2 ⟨argmax_0_eq h0 h1 _ (h 0), argmax_1_eq h0 h1 _ (h 1)⟩)
  · rintro rfl
    unfold Game.Realizes
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨isArgmaxH_01 h0 h1, isArgmaxH_10 h0 h1⟩

/-- `π* = aa` is the unique maximizer.
Source: [[updateless-self-game]] §2 (Theorem A, "unique maximizer")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem unique_max (π : Fin 2 → Fin 2) (hne : π ≠ (game δ h0 h1).piStar) :
    (game δ h0 h1).U π < (game δ h0 h1).Ustar := by
  rw [Ustar_eq, U_apply]
  unfold Ufun
  have := η_pos h0 h1
  split_ifs with ha hb hb
  · exfalso; apply hne
    exact funext (Fin.forall_fin_two.2 ⟨by simp [ha, piStar_eq], by simp [hb, piStar_eq]⟩)
  · norm_num
  · norm_num
  · linarith

/-- **Theorem A (the proposed theorem refuted, uniformly in `δ`)**: for every `δ ∈ (0,1)` there is a
two-situation, two-action game with `δ` as its prior, `U* = 1`, `π*` the unique maximizer, every action
available at both situations (convention-free), a strict Herrmann argmax at both, the trust bound at both,
and every realized policy of utility `0` — loss `= U* = 1`, at every `δ`; the realized policy `ba` exists.
Refutes: [[summer-research-plan-2026--research-ideas-may-2026]] line 48 in the pointwise-EDT static-belief
reading with `ε(δ) → 0` uniformly over instances (ATTRIBUTION-UNVETTED reading); the founding sketch's
"two situations cannot do this"; Idea 2's `O(δ)`; Idea 7's `δ`-interpolation; Prop 2★. Surviving
neighbours: `theoremB` (margin), `theoremC` (self-consistency + trust bound).
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static belief; not
rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §2 (Theorem A); [[uea-inventory]] 023; [[00-founding-sketches]] §3
Kind: P
Fidelity: exact (general `δ`, not sampled)
Hyps: (a) -/
theorem theoremA (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ G : Game (Fin 2) (Fin 2), G.δ = δ ∧ G.Ustar = 1 ∧
      (∀ π, π ≠ G.piStar → G.U π < G.Ustar) ∧
      (∀ s a, avail G.mu s a) ∧
      G.StrictArgmax G.mu ∧
      (∀ s, G.TB G.mu s) ∧
      (∀ π, G.Realizes G.mu π → G.U π = 0) ∧
      (∃ π, G.Realizes G.mu π) :=
  ⟨game δ h0 h1, rfl, Ustar_eq h0 h1, unique_max h0 h1, avail_all h0 h1, strictArgmax h0 h1,
    TB_all h0 h1, fun π hπ => by
      rw [(realizes_iff h0 h1 π).1 hπ, U_apply]; simp [Ufun],
    ⟨![1, 0], (realizes_iff h0 h1 _).2 rfl⟩⟩

/-- The loss is exactly `U* = 1` for every realized policy and every `δ ∈ (0,1)`: no `δ`-scaling.
Source: [[updateless-self-game]] §3.4 ("The worst gap does not scale with `δ` at all; it is exactly `1`");
[[findings--unbounded-embedded-agency-ideate]] Idea 2 (`O(δ)` clause, refuted), Idea 7 (`δ`-interpolation,
refuted)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem loss_eq_one (π : Fin 2 → Fin 2) (hπ : (game δ h0 h1).Realizes (game δ h0 h1).mu π) :
    (game δ h0 h1).Ustar - (game δ h0 h1).U π = 1 := by
  rw [(realizes_iff h0 h1 π).1 hπ, U_apply, Ustar_eq]; simp [Ufun]

end TheoremA

end Cleanroom.Uea.UeaSelfGame
