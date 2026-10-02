import Cleanroom.Lit.LitDdbAccuracyMm.MM.Refute
import Cleanroom.Lit.LitDdbAccuracyMm.MM.Value

/-!
# MM Theorem 3.4 (⟸) refuted on a non-twin frame (audit r1 repair, B2(b))

The round-1 audits graded the two-world refutation of the "if" direction
(`mm34_backward_refuted_twin`) N−: there the agent is the principal's twin, so strict agreement
is the identity of two preference orders. The adversarial audit conjectured that with Boolean
consequences, a common `V` and a rich act set every such refutation is a twin up to a positive
affine change of `V`. It is not: strict agreement is one-directional (principal-strict ⟹
agent-strict), so it does not force the two expected-utility orders to agree.

**The frame `G3`**: three worlds, one type cell, agent beliefs `(2/5, 3/10, 3/10)` at every
world, `V = u = uB` (`true ↦ 1`, `false ↦ 0`), all eight Boolean acts admissible; the principal
`π = (⅓, ⅓, ⅓)`. The principal ranks acts by the number of worlds where they are `true`; the
agent's values are `0, 3/10, 3/10, 3/5, 2/5, 7/10, 7/10, 1` for
`fff, fft, ftf, ftt, tff, tft, ttf, ttt`. Since `min(size s + 1) > max(size s)` (`3/10 > 0`,
`3/5 > 2/5`, `1 > 7/10`), a strict principal preference is a strict agent preference: strict
agreement holds, and the agent is not a twin (`G3_not_twin`). The agent ties on `{ftf, fft}` and
on `{ttf, tft}`; the behaviour `B4` breaks each tie world-by-world so that both tied acts are
chosen at `π`-positive worlds (stochastic choice, both forms) and, on `{ftf, fft}`, so that the
chosen act is `false` at the current world: delegation of that menu is worth `0 < ⅓ = E_π(ftf)`,
so `π` does not value `B4`. Clarity is vacuous (one cell), richness and constant acts trivial.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The three-world Boolean frame -/

/-- The agent's beliefs at every world of `G3`: `(2/5, 3/10, 3/10)`.
Source: audit r1 (fidelity) B2 (the three-world non-twin instance)
Kind: D
Fidelity: n/a -/
def pag3 : Fin 3 → ℝ := ![2 / 5, 3 / 10, 3 / 10]

/-- `pag3` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pag3_mem : pag3 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The non-twin generalized frame**: agent beliefs `pag3` at every world, `V_ω = u = uB`, all
eight Boolean acts admissible — one type cell, clarity vacuous, richness and constant acts
trivial.
Source: audit r1 (fidelity) B2
Kind: D
Fidelity: n/a -/
def G3 : GFrame (Fin 3) Bool where
  u := uB
  Pag := fun _ => pag3
  Pag_mem := fun _ => pag3_mem
  V := fun _ => uB
  A := univ

/-- The eight acts on three worlds: `(false, false, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fff3 : Fin 3 → Bool := ![false, false, false]

/-- `(false, false, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fft3 : Fin 3 → Bool := ![false, false, true]

/-- `(false, true, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ftf3 : Fin 3 → Bool := ![false, true, false]

/-- `(false, true, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ftt3 : Fin 3 → Bool := ![false, true, true]

/-- `(true, false, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tff3 : Fin 3 → Bool := ![true, false, false]

/-- `(true, false, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tft3 : Fin 3 → Bool := ![true, false, true]

/-- `(true, true, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ttf3 : Fin 3 → Bool := ![true, true, false]

/-- `(true, true, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ttt3 : Fin 3 → Bool := ![true, true, true]

/-- The first coordinate of a Boolean three-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bvec3_zero (a b c : Bool) : (![a, b, c] : Fin 3 → Bool) 0 = a := rfl

/-- The second coordinate of a Boolean three-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bvec3_one (a b c : Bool) : (![a, b, c] : Fin 3 → Bool) 1 = b := rfl

/-- The third coordinate of a Boolean three-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bvec3_two (a b c : Bool) : (![a, b, c] : Fin 3 → Bool) 2 = c := rfl

/-- `uB true = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uB_true : uB true = 1 := by simp [uB]

/-- `uB false = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uB_false : uB false = 0 := by simp [uB]

/-- Every act on three worlds is one of the eight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem act_cases3 (a : Fin 3 → Bool) :
    a = fff3 ∨ a = fft3 ∨ a = ftf3 ∨ a = ftt3 ∨ a = tff3 ∨ a = tft3 ∨ a = ttf3 ∨ a = ttt3 := by
  have h : a = ![a 0, a 1, a 2] := by
    ext w; fin_cases w <;> rfl
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;> rw [h, h0, h1, h2]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-- The agent's expected utility on `G3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_agentEU (ω : Fin 3) (a : Fin 3 → Bool) :
    G3.agentEU ω a = 2 / 5 * uB (a 0) + 3 / 10 * uB (a 1) + 3 / 10 * uB (a 2) := by
  simp [GFrame.agentEU, G3, E, Fin.sum_univ_three, pag3, vec3_two]

/-- The agent's values of the eight acts: `0, 3/10, 3/10, 3/5, 2/5, 7/10, 7/10, 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_agentEU_vals (ω : Fin 3) :
    G3.agentEU ω fff3 = 0 ∧ G3.agentEU ω fft3 = 3 / 10 ∧ G3.agentEU ω ftf3 = 3 / 10 ∧
    G3.agentEU ω ftt3 = 3 / 5 ∧ G3.agentEU ω tff3 = 2 / 5 ∧ G3.agentEU ω tft3 = 7 / 10 ∧
    G3.agentEU ω ttf3 = 7 / 10 ∧ G3.agentEU ω ttt3 = 1 := by
  simp only [G3_agentEU, fff3, fft3, ftf3, ftt3, tff3, tft3, ttf3, ttt3, bvec3_zero, bvec3_one,
    bvec3_two, uB_true, uB_false]
  norm_num

/-- The type cell of every world of `G3` is everything.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_tcell (ω : Fin 3) : tcell G3 ω = univ := by
  ext w; simp [tcell, G3]

/-- Clarity holds on `G3` (vacuously).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_clarity : Clarity G3 := by
  intro ω ω' h
  rw [G3_tcell] at h
  exact absurd (mem_univ ω') h

/-- Richness holds on `G3` (all acts admissible).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_richness : Richness G3 := fun _ _ _ _ _ => mem_univ _

/-- Constant acts hold on `G3` (`ttt3` and `fff3`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_constantActs : ConstantActs G3 :=
  ⟨true, false, by simp [G3, uB], mem_univ _, mem_univ _⟩

/-- **`G3` is not a twin frame**: the agent's beliefs differ from the principal's `unif3` (and,
both being distributions on the one cell, are not proportional to it either).
Source: audit r1 (adversarial) B2(b) (the twin conjecture)
Kind: L
Fidelity: n/a -/
theorem G3_not_twin (ω : Fin 3) : G3.Pag ω ≠ unif3 := by
  intro h
  have := congrFun h 0
  norm_num [G3, pag3, unif3] at this

/-! ## The behaviour `B4` -/

/-- Priority at worlds `0` and `1`: agent-optimal first; ties broken `tft ≻ ttf`, `fft ≻ ftf`.
Source: none: infrastructure (an instance of MM Definition 3.3's `B_ω`)
Kind: D
Fidelity: n/a -/
def choiceA (𝒜 : Finset (Fin 3 → Bool)) : Fin 3 → Bool :=
  if ttt3 ∈ 𝒜 then ttt3 else if tft3 ∈ 𝒜 then tft3 else if ttf3 ∈ 𝒜 then ttf3 else
  if ftt3 ∈ 𝒜 then ftt3 else if tff3 ∈ 𝒜 then tff3 else if fft3 ∈ 𝒜 then fft3 else
  if ftf3 ∈ 𝒜 then ftf3 else fff3

/-- Priority at world `2`: ties broken `ttf ≻ tft`, `ftf ≻ fft`.
Source: none: infrastructure (an instance of MM Definition 3.3's `B_ω`)
Kind: D
Fidelity: n/a -/
def choiceB (𝒜 : Finset (Fin 3 → Bool)) : Fin 3 → Bool :=
  if ttt3 ∈ 𝒜 then ttt3 else if ttf3 ∈ 𝒜 then ttf3 else if tft3 ∈ 𝒜 then tft3 else
  if ftt3 ∈ 𝒜 then ftt3 else if tff3 ∈ 𝒜 then tff3 else if ftf3 ∈ 𝒜 then ftf3 else
  if fft3 ∈ 𝒜 then fft3 else fff3

/-- **The behaviour of the non-twin refutation**: `choiceA` at worlds `0, 1`, `choiceB` at
world `2` — on the tie `{ftf, fft}` it picks the act that is `false` at the current world.
Source: audit r1 (fidelity) B2
Kind: D
Fidelity: n/a (an instance of MM Definition 3.3's `B_ω`) -/
def B4 (ω : Fin 3) (𝒜 : Finset (Fin 3 → Bool)) : Fin 3 → Bool :=
  if ω = 2 then choiceB 𝒜 else choiceA 𝒜

/-- `B4` at world `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B4_two (𝒜 : Finset (Fin 3 → Bool)) : B4 2 𝒜 = choiceB 𝒜 := by simp [B4]

/-- `B4` at worlds `0` and `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B4_of_ne {ω : Fin 3} (h : ω ≠ 2) (𝒜 : Finset (Fin 3 → Bool)) : B4 ω 𝒜 = choiceA 𝒜 := by
  simp [B4, h]

/-- A nonempty menu missing the seven other acts contains `fff3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fff3_mem_of {𝒜 : Finset (Fin 3 → Bool)} (hne : 𝒜.Nonempty) (h1 : ttt3 ∉ 𝒜)
    (h2 : tft3 ∉ 𝒜) (h3 : ttf3 ∉ 𝒜) (h4 : ftt3 ∉ 𝒜) (h5 : tff3 ∉ 𝒜) (h6 : fft3 ∉ 𝒜)
    (h7 : ftf3 ∉ 𝒜) : fff3 ∈ 𝒜 := by
  obtain ⟨a, ha⟩ := hne
  rcases act_cases3 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact absurd ha h6
  · exact absurd ha h7
  · exact absurd ha h4
  · exact absurd ha h5
  · exact absurd ha h2
  · exact absurd ha h3
  · exact absurd ha h1

/-- An act is agent-optimal in a menu once every act of strictly greater agent value is absent
(the same condition for both priority orders, which differ only within ties).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem opt3_of_mem {𝒜 : Finset (Fin 3 → Bool)} (ω : Fin 3) (c : Fin 3 → Bool)
    (hc : c = ttt3 ∨ (c = tft3 ∧ ttt3 ∉ 𝒜) ∨ (c = ttf3 ∧ ttt3 ∉ 𝒜) ∨
      (c = ftt3 ∧ ttt3 ∉ 𝒜 ∧ tft3 ∉ 𝒜 ∧ ttf3 ∉ 𝒜) ∨
      (c = tff3 ∧ ttt3 ∉ 𝒜 ∧ tft3 ∉ 𝒜 ∧ ttf3 ∉ 𝒜 ∧ ftt3 ∉ 𝒜) ∨
      (c = fft3 ∧ ttt3 ∉ 𝒜 ∧ tft3 ∉ 𝒜 ∧ ttf3 ∉ 𝒜 ∧ ftt3 ∉ 𝒜 ∧ tff3 ∉ 𝒜) ∨
      (c = ftf3 ∧ ttt3 ∉ 𝒜 ∧ tft3 ∉ 𝒜 ∧ ttf3 ∉ 𝒜 ∧ ftt3 ∉ 𝒜 ∧ tff3 ∉ 𝒜) ∨
      (c = fff3 ∧ ttt3 ∉ 𝒜 ∧ tft3 ∉ 𝒜 ∧ ttf3 ∉ 𝒜 ∧ ftt3 ∉ 𝒜 ∧ tff3 ∉ 𝒜 ∧ fft3 ∉ 𝒜 ∧
        ftf3 ∉ 𝒜)) :
    ∀ a ∈ 𝒜, G3.agentEU ω a ≤ G3.agentEU ω c := by
  intro a ha
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := G3_agentEU_vals ω
  rcases act_cases3 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, h4⟩ |
      ⟨rfl, h1, h2, h3, h4, h5⟩ | ⟨rfl, h1, h2, h3, h4, h5⟩ | ⟨rfl, h1, h2, h3, h4, h5, h6, h7⟩ <;>
    first
      | exact absurd ha ‹_›
      | (simp only [v0, v1, v2, v3, v4, v5, v6, v7]; norm_num)

/-- `choiceA` is an agent-optimal act of the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_spec {𝒜 : Finset (Fin 3 → Bool)} (hne : 𝒜.Nonempty) (ω : Fin 3) :
    choiceA 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, G3.agentEU ω a ≤ G3.agentEU ω (choiceA 𝒜) := by
  by_cases h1 : ttt3 ∈ 𝒜
  · rw [choiceA, if_pos h1]
    exact ⟨h1, opt3_of_mem ω ttt3 (Or.inl rfl)⟩
  by_cases h2 : tft3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_pos h2]
    exact ⟨h2, opt3_of_mem ω tft3 (Or.inr (Or.inl ⟨rfl, h1⟩))⟩
  by_cases h3 : ttf3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_neg h2, if_pos h3]
    exact ⟨h3, opt3_of_mem ω ttf3 (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩)))⟩
  by_cases h4 : ftt3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact ⟨h4, opt3_of_mem ω ftt3 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2, h3⟩))))⟩
  by_cases h5 : tff3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    exact ⟨h5, opt3_of_mem ω tff3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2, h3, h4⟩)))))⟩
  by_cases h6 : fft3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    exact ⟨h6, opt3_of_mem ω fft3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2, h3, h4, h5⟩))))))⟩
  by_cases h7 : ftf3 ∈ 𝒜
  · rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    exact ⟨h7, opt3_of_mem ω ftf3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2, h3, h4, h5⟩)))))))⟩
  · rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
    exact ⟨fff3_mem_of hne h1 h2 h3 h4 h5 h6 h7, opt3_of_mem ω fff3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, h1, h2, h3, h4, h5, h6, h7⟩)))))))⟩

/-- `choiceB` is an agent-optimal act of the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_spec {𝒜 : Finset (Fin 3 → Bool)} (hne : 𝒜.Nonempty) (ω : Fin 3) :
    choiceB 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, G3.agentEU ω a ≤ G3.agentEU ω (choiceB 𝒜) := by
  by_cases h1 : ttt3 ∈ 𝒜
  · rw [choiceB, if_pos h1]
    exact ⟨h1, opt3_of_mem ω ttt3 (Or.inl rfl)⟩
  by_cases h2 : ttf3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_pos h2]
    exact ⟨h2, opt3_of_mem ω ttf3 (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩)))⟩
  by_cases h3 : tft3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_neg h2, if_pos h3]
    exact ⟨h3, opt3_of_mem ω tft3 (Or.inr (Or.inl ⟨rfl, h1⟩))⟩
  by_cases h4 : ftt3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact ⟨h4, opt3_of_mem ω ftt3 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h3, h2⟩))))⟩
  by_cases h5 : tff3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    exact ⟨h5, opt3_of_mem ω tff3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h3, h2, h4⟩)))))⟩
  by_cases h6 : ftf3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    exact ⟨h6, opt3_of_mem ω ftf3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h3, h2, h4, h5⟩)))))))⟩
  by_cases h7 : fft3 ∈ 𝒜
  · rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
    exact ⟨h7, opt3_of_mem ω fft3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h3, h2, h4, h5⟩))))))⟩
  · rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
    exact ⟨fff3_mem_of hne h1 h3 h2 h4 h5 h7 h6, opt3_of_mem ω fff3
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, h1, h3, h2, h4, h5, h7, h6⟩)))))))⟩

/-- `B4` is a behaviour on `G3`.
Source: audit r1 (fidelity) B2
Kind: L
Fidelity: n/a -/
theorem B4_isBehaviour : IsBehaviour G3 B4 := by
  intro ω 𝒜 _ hne
  by_cases h : ω = 2
  · rw [B4, if_pos h]; exact choiceB_spec hne ω
  · rw [B4, if_neg h]; exact choiceA_spec hne ω

/-! ## Reading the choice functions off a chosen act -/

/-- If `choiceA 𝒜 = c ≠ ttt3` then `ttt3 ∉ 𝒜`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_ttt3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (hne : c ≠ ttt3) : ttt3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_pos h] at hc; exact hne hc.symm

/-- If `choiceA 𝒜 = c ≠ tft3` and `ttt3 ∉ 𝒜` then `tft3 ∉ 𝒜`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_tft3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (hne : c ≠ tft3) : tft3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_neg h1, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceA`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_ttf3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : tft3 ∉ 𝒜) (hne : c ≠ ttf3) : ttf3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_neg h1, if_neg h2, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceA`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_ftt3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : tft3 ∉ 𝒜) (h3 : ttf3 ∉ 𝒜) (hne : c ≠ ftt3) : ftt3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceA`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_tff3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : tft3 ∉ 𝒜) (h3 : ttf3 ∉ 𝒜) (h4 : ftt3 ∉ 𝒜) (hne : c ≠ tff3) :
    tff3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h] at hc
  exact hne hc.symm

/-- The next position of `choiceA`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceA_notMem_fft3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceA 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : tft3 ∉ 𝒜) (h3 : ttf3 ∉ 𝒜) (h4 : ftt3 ∉ 𝒜) (h5 : tff3 ∉ 𝒜)
    (hne : c ≠ fft3) : fft3 ∉ 𝒜 := by
  intro h; rw [choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h] at hc
  exact hne hc.symm

/-- If `choiceB 𝒜 = c ≠ ttt3` then `ttt3 ∉ 𝒜`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_ttt3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (hne : c ≠ ttt3) : ttt3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_ttf3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (hne : c ≠ ttf3) : ttf3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_neg h1, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_tft3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : ttf3 ∉ 𝒜) (hne : c ≠ tft3) : tft3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_neg h1, if_neg h2, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_ftt3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : ttf3 ∉ 𝒜) (h3 : tft3 ∉ 𝒜) (hne : c ≠ ftt3) : ftt3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_pos h] at hc; exact hne hc.symm

/-- The next position of `choiceB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_tff3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : ttf3 ∉ 𝒜) (h3 : tft3 ∉ 𝒜) (h4 : ftt3 ∉ 𝒜) (hne : c ≠ tff3) :
    tff3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h] at hc
  exact hne hc.symm

/-- The next position of `choiceB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choiceB_notMem_ftf3 {𝒜 : Finset (Fin 3 → Bool)} {c : Fin 3 → Bool} (hc : choiceB 𝒜 = c)
    (h1 : ttt3 ∉ 𝒜) (h2 : ttf3 ∉ 𝒜) (h3 : tft3 ∉ 𝒜) (h4 : ftt3 ∉ 𝒜) (h5 : tff3 ∉ 𝒜)
    (hne : c ≠ ftf3) : ftf3 ∉ 𝒜 := by
  intro h; rw [choiceB, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h] at hc
  exact hne hc.symm

/-- The distinctness facts the tie-break arguments use.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem acts3_distinct :
    tft3 ≠ ttt3 ∧ ttf3 ≠ ttt3 ∧ tft3 ≠ ttf3 ∧ ttf3 ≠ tft3 ∧
    fft3 ≠ ttt3 ∧ fft3 ≠ tft3 ∧ fft3 ≠ ttf3 ∧ fft3 ≠ ftt3 ∧ fft3 ≠ tff3 ∧ fft3 ≠ ftf3 ∧
    ftf3 ≠ ttt3 ∧ ftf3 ≠ tft3 ∧ ftf3 ≠ ttf3 ∧ ftf3 ≠ ftt3 ∧ ftf3 ≠ tff3 ∧ ftf3 ≠ fft3 := by
  simp only [fft3, ftf3, ftt3, tff3, tft3, ttf3, ttt3]
  decide

/-! ## The refutation's conjuncts -/

/-- Agent ties on `G3` are equalities or one of the two tied pairs.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tie_cases3 {ω : Fin 3} {a b : Fin 3 → Bool} (h : G3.agentEU ω a = G3.agentEU ω b) :
    a = b ∨ (a = tft3 ∧ b = ttf3) ∨ (a = ttf3 ∧ b = tft3) ∨ (a = fft3 ∧ b = ftf3) ∨
      (a = ftf3 ∧ b = fft3) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := G3_agentEU_vals ω
  rcases act_cases3 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases act_cases3 b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (norm_num [v0, v1, v2, v3, v4, v5, v6, v7] at h; done)
      | simp

/-- **Stochastic choice for `B4` (`V`-form)**: every act tied with a chosen act is chosen at some
`π`-positive world of the (unique) type.
Source: audit r1 (fidelity) B2; MM App. D l. 417
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem stochasticChoiceV_unif3_B4 : StochasticChoiceV G3 unif3 B4 := by
  intro 𝒜 _ a ha b hb ω htie hB
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16⟩ :=
    acts3_distinct
  have hpos : ∀ ω' : Fin 3, 0 < unif3 ω' := by
    intro ω'; fin_cases ω' <;> norm_num [unif3]
  have hcell : ∀ ω', ω' ∈ tcell G3 ω := fun ω' => by rw [G3_tcell]; exact mem_univ _
  rcases tie_cases3 htie with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ω, hpos ω, hcell ω, hB⟩
  · -- `tft3` chosen: at `ω ≠ 2` world `2` picks `ttf3`; at `ω = 2` impossible
    by_cases h2 : ω = 2
    · exfalso
      rw [B4, if_pos h2] at hB
      have h1 := choiceB_notMem_ttt3 hB d1
      exact choiceB_notMem_ttf3 hB h1 d3 hb
    · rw [B4, if_neg h2] at hB
      have h1 := choiceA_notMem_ttt3 hB d1
      exact ⟨2, hpos 2, hcell 2, by rw [B4_two, choiceB, if_neg h1, if_pos hb]⟩
  · -- `ttf3` chosen: at `ω = 2` world `0` picks `tft3`; at `ω ≠ 2` impossible
    by_cases h2 : ω = 2
    · rw [B4, if_pos h2] at hB
      have h1 := choiceB_notMem_ttt3 hB d2
      exact ⟨0, hpos 0, hcell 0, by
        rw [B4_of_ne (by decide), choiceA, if_neg h1, if_pos hb]⟩
    · exfalso
      rw [B4, if_neg h2] at hB
      have h1 := choiceA_notMem_ttt3 hB d2
      exact choiceA_notMem_tft3 hB h1 d4 hb
  · -- `fft3` chosen: at `ω ≠ 2` world `2` picks `ftf3`; at `ω = 2` impossible
    by_cases h2 : ω = 2
    · exfalso
      rw [B4, if_pos h2] at hB
      have h1 := choiceB_notMem_ttt3 hB d5
      have h3 := choiceB_notMem_ttf3 hB h1 d7
      have h4 := choiceB_notMem_tft3 hB h1 h3 d6
      have h5 := choiceB_notMem_ftt3 hB h1 h3 h4 d8
      have h6 := choiceB_notMem_tff3 hB h1 h3 h4 h5 d9
      exact choiceB_notMem_ftf3 hB h1 h3 h4 h5 h6 d10 hb
    · rw [B4, if_neg h2] at hB
      have h1 := choiceA_notMem_ttt3 hB d5
      have h3 := choiceA_notMem_tft3 hB h1 d6
      have h4 := choiceA_notMem_ttf3 hB h1 h3 d7
      have h5 := choiceA_notMem_ftt3 hB h1 h3 h4 d8
      have h6 := choiceA_notMem_tff3 hB h1 h3 h4 h5 d9
      exact ⟨2, hpos 2, hcell 2, by
        rw [B4_two, choiceB, if_neg h1, if_neg h4, if_neg h3, if_neg h5, if_neg h6, if_pos hb]⟩
  · -- `ftf3` chosen: at `ω = 2` world `0` picks `fft3`; at `ω ≠ 2` impossible
    by_cases h2 : ω = 2
    · rw [B4, if_pos h2] at hB
      have h1 := choiceB_notMem_ttt3 hB d11
      have h3 := choiceB_notMem_ttf3 hB h1 d13
      have h4 := choiceB_notMem_tft3 hB h1 h3 d12
      have h5 := choiceB_notMem_ftt3 hB h1 h3 h4 d14
      have h6 := choiceB_notMem_tff3 hB h1 h3 h4 h5 d15
      exact ⟨0, hpos 0, hcell 0, by
        rw [B4_of_ne (by decide), choiceA, if_neg h1, if_neg h4, if_neg h3, if_neg h5, if_neg h6,
          if_pos hb]⟩
    · exfalso
      rw [B4, if_neg h2] at hB
      have h1 := choiceA_notMem_ttt3 hB d11
      have h3 := choiceA_notMem_tft3 hB h1 d12
      have h4 := choiceA_notMem_ttf3 hB h1 h3 d13
      have h5 := choiceA_notMem_ftt3 hB h1 h3 h4 d14
      have h6 := choiceA_notMem_tff3 hB h1 h3 h4 h5 d15
      exact choiceA_notMem_fft3 hB h1 h3 h4 h5 h6 d16 hb

/-- On `G3` the printed (`u`) and intended (`V_ω`) stochastic-choice conditions coincide
(`V = u`), so the `u`-form conjunct of the refutation is not independent evidence about the
printed form.
Source: none: infrastructure (`V_ω = u`)
Kind: L
Fidelity: n/a -/
theorem stochasticChoiceU_iff_V_G3 (π : Fin 3 → ℝ)
    (B : Fin 3 → Finset (Fin 3 → Bool) → (Fin 3 → Bool)) :
    StochasticChoiceU G3 π B ↔ StochasticChoiceV G3 π B := Iff.rfl

/-- The principal's conditional expected utility on the one cell of `G3` is the number of `true`s
over three.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G3_cellEU (ω : Fin 3) (c : Fin 3 → Bool) :
    cellEU unif3 G3 ω c = (uB (c 0) + uB (c 1) + uB (c 2)) / 3 := by
  simp only [cellEU]
  rw [G3_tcell]
  simp only [Fin.sum_univ_three, unif3, G3, vec3_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Strict agreement holds on `G3` with `π = unif3`, although the agent is not a twin**: a
strict principal preference is a strictly larger number of `true`s, and every act with `k + 1`
`true`s has agent value above every act with `k` (`3/10 > 0`, `3/5 > 2/5`, `1 > 7/10`).
Source: audit r1 (fidelity) B2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem strictAgree_unif3_G3 : StrictAgree unif3 G3 := by
  intro a _ b _ ω _ hlt
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := G3_agentEU_vals ω
  rw [G3_cellEU, G3_cellEU] at hlt
  rcases act_cases3 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases act_cases3 b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7] <;>
    simp only [fff3, fft3, ftf3, ftt3, tff3, tft3, ttf3, ttt3, bvec3_zero, bvec3_one, bvec3_two,
      uB_true, uB_false] at hlt <;>
    first
      | (norm_num at hlt; done)
      | norm_num

/-- **Valuing fails for `B4`**: on `{ftf3, fft3}` the behaviour picks the act that is `false` at
the current world (`fft3` at worlds `0, 1`, `ftf3` at world `2`), so delegation is worth `0`,
while `ftf3` is worth `⅓`.
Source: audit r1 (fidelity) B2
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_valuesB_unif3_B4 : ¬ ValuesB unif3 G3 B4 := by
  intro h
  have hmem : ∀ x, x ∈ ({ftf3, fft3} : Finset (Fin 3 → Bool)) ↔ x = ftf3 ∨ x = fft3 := by
    intro x; simp only [mem_insert, mem_singleton]
  have h1 : ttt3 ∉ ({ftf3, fft3} : Finset (Fin 3 → Bool)) := by
    rw [hmem]; simp only [ttt3, ftf3, fft3]; decide
  have h2 : tft3 ∉ ({ftf3, fft3} : Finset (Fin 3 → Bool)) := by
    rw [hmem]; simp only [tft3, ftf3, fft3]; decide
  have h3 : ttf3 ∉ ({ftf3, fft3} : Finset (Fin 3 → Bool)) := by
    rw [hmem]; simp only [ttf3, ftf3, fft3]; decide
  have h4 : ftt3 ∉ ({ftf3, fft3} : Finset (Fin 3 → Bool)) := by
    rw [hmem]; simp only [ftt3, ftf3, fft3]; decide
  have h5 : tff3 ∉ ({ftf3, fft3} : Finset (Fin 3 → Bool)) := by
    rw [hmem]; simp only [tff3, ftf3, fft3]; decide
  have hb0 : B4 0 {ftf3, fft3} = fft3 := by
    rw [B4_of_ne (by decide), choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_pos (mem_insert_of_mem (mem_singleton_self _))]
  have hb1 : B4 1 {ftf3, fft3} = fft3 := by
    rw [B4_of_ne (by decide), choiceA, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_pos (mem_insert_of_mem (mem_singleton_self _))]
  have hb2 : B4 2 {ftf3, fft3} = ftf3 := by
    rw [B4_two, choiceB, if_neg h1, if_neg h3, if_neg h2, if_neg h4, if_neg h5,
      if_pos (mem_insert_self _ _)]
  have := h {ftf3, fft3} (subset_univ _) (insert_nonempty _ _) ftf3 (mem_insert_self _ _)
  simp only [delegValue, Fin.sum_univ_three] at this
  rw [hb0, hb1, hb2] at this
  simp only [E, Function.comp, G3, unif3, ftf3, fft3, Fin.sum_univ_three, bvec3_two, vec3_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, uB_true, uB_false] at this
  norm_num at this

/-- **MM Theorem 3.4 (⟸) as printed is false, on a non-twin frame.** On `G3` (three worlds,
one type cell, agent beliefs `(2/5, 3/10, 3/10) ≠ π = (⅓, ⅓, ⅓)`, `V = u`, all eight Boolean
acts): strict agreement, stochastic choice (both forms; they coincide since `V = u`), clarity
(vacuous: one cell), richness and constant acts hold, yet the behaviour `B4` — which breaks the
agent's tie on `{ftf, fft}` toward the act that is `false` at the current world — is not
valued (`0 < ⅓`). The reading is MM's own: Definition 3.3 lets `B_ω` vary within a type cell,
and Appendix D's stochastic choice presupposes that it does
(`no_typeMeasurable_stochasticChoice_G2`). The twin version on two worlds is
`mm34_backward_refuted_twin` (N−).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97,
App. D l. 421 (the "if" direction, never proved in App. D); reading: `B_ω` world-indexed within a
cell (Definition 3.3), ATTRIBUTION-UNVETTED; surviving neighbour
`typeMeasurable_valuesB_iff_strictAgree`; item 086; audit r1 B2(b)
Kind: N+
Fidelity: exact (refutes the printed statement under the literal reading)
Hyps: (a) none -/
theorem mm34_backward_refuted :
    IsBehaviour G3 B4 ∧ StrictAgree unif3 G3 ∧ StochasticChoiceU G3 unif3 B4 ∧
    StochasticChoiceV G3 unif3 B4 ∧ Clarity G3 ∧ Richness G3 ∧ ConstantActs G3 ∧
    ¬ ValuesB unif3 G3 B4 :=
  ⟨B4_isBehaviour, strictAgree_unif3_G3, stochasticChoiceV_unif3_B4, stochasticChoiceV_unif3_B4,
    G3_clarity, G3_richness, G3_constantActs, not_valuesB_unif3_B4⟩

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM
