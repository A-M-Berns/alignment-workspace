import Cleanroom.Lit.LitDdbAccuracyMm.MM.Theorem34

/-!
# MM Theorem 3.4 as printed is false in both directions; the Rain example (Target 15 (ii), (iii), (vi))

The printed theorem (App. D l. 421): "Let `⟨Ω, F, π, u, B, A, C⟩` be a generalized frame with
`B = (P, V)` satisfying stochastic choice and clarity. Suppose that `A` satisfies richness and
constant acts. Then `π` values `(P, V)` if and only if for any acts `a, b ∈ A` and every `ω ∈ Ω`,
if `E_π(u(a) | [ω]) > E_π(u(b) | [ω])` then `E_ω(V_ω(a)) > E_ω(V_ω(b))`."

Reading (literal): `B_ω` is any world-indexed argmax selection (Definition 3.3 lets it depend on
`ω` within a type cell). Both refutations live on **two worlds, one type cell**: the agent has
uniform beliefs and the principal's utility (`V_ω = u`, `u(true) = 1`, `u(false) = 0`), so it is
indifferent exactly between `(true, false)` and `(false, true)`.

* **(ii) ⟹ fails** (`mm34_forward_refuted`): `π = (2/3, 1/3)` and the behaviour that, on a tie,
  takes the act that is `true` at the current world. Delegation is then worth
  `π(some top act is true here)`, which is at least every option's value, so `π` values the
  behaviour; stochastic choice holds (each tied act is chosen at some `π`-positive world);
  clarity, richness, constant acts hold; yet the principal strictly prefers `(true, false)`
  (value `2/3`) to `(false, true)` (value `1/3`) while the agent ties.
* **(iii) ⟸ fails, twin version** (`mm34_backward_refuted_twin`, graded N− since audit r1):
  `π = (1/2, 1/2)`, the agent is the principal's twin (so strict agreement is the identity of two
  preference orders), and the behaviour breaks the one tie *adversarially* (world `0` picks
  `(false, true)`, world `1` picks `(true, false)`): on that menu delegation is worth `0 < 1/2`.
  The **non-twin** refutation of (⟸) — three worlds, agent beliefs `(2/5, 3/10, 3/10)` against
  `π = (⅓, ⅓, ⅓)` — is `mm34_backward_refuted` in `MM/Refute3.lean`.

The surviving neighbour is `typeMeasurable_valuesB_iff_strictAgree` (`MM/Theorem34.lean`).
`no_typeMeasurable_stochasticChoice_G2` (from the round-1 adversarial audit's probe) shows that
MM's stochastic-choice postulate itself presupposes a world-indexed `B_ω`: on `G2` no
type-measurable behaviour satisfies it, for any `π`.

The mandate suggested a three-world instance for (ii); two worlds suffice, which is what is
formalised (the report says so).

**(vi) The Rain example** (`MM/Refute.lean`, `rain_*`): four worlds `(Rain?, type?)`, the
principal thinks the agent underconfident, the bets `g_x = (1 − x)` on Rain / `−x` off; for the
menus `{g_x, 0}` every behaviour is valued for every `x ∈ [0, 1]`, yet strict agreement fails at
`x = 9/10` — richness is load-bearing.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The two-world Boolean frame -/

/-- The principal's utility on `Bool`: `u(true) = 1`, `u(false) = 0`.
Source: none: infrastructure (Target 15 (ii)/(iii))
Kind: D
Fidelity: n/a -/
def uB : Bool → ℝ := fun b => if b then 1 else 0

/-- The four acts on two worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tt : Fin 2 → Bool := ![true, true]

/-- `(true, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tf : Fin 2 → Bool := ![true, false]

/-- `(false, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ft : Fin 2 → Bool := ![false, true]

/-- `(false, false)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ff : Fin 2 → Bool := ![false, false]

/-- Every act on two worlds is one of the four.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem act_cases (a : Fin 2 → Bool) : a = tt ∨ a = tf ∨ a = ft ∨ a = ff := by
  have h : a = ![a 0, a 1] := by
    ext w; fin_cases w <;> rfl
  cases h0 : a 0 <;> cases h1 : a 1 <;> rw [h, h0, h1]
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- **The generalized frame of both refutations**: uniform agent beliefs at both worlds, the
agent's utility equal to the principal's (`V_ω = u = uB`), all four acts admissible — one type
cell, clarity vacuous, richness and constant acts trivial.
Source: mandate Target 15 (ii)/(iii)
Kind: D
Fidelity: n/a -/
def G2 : GFrame (Fin 2) Bool where
  u := uB
  Pag := fun _ => half
  Pag_mem := fun _ => half_mem
  V := fun _ => uB
  A := univ

/-- The deferrer of refutation (ii): `π = (2/3, 1/3)`.
Source: mandate Target 15 (ii)
Kind: D
Fidelity: n/a -/
def π2 : Fin 2 → ℝ := ![2 / 3, 1 / 3]

/-- `π2` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π2_mem : π2 ∈ stdSimplex ℝ (Fin 2) :=
  simplex2 _ _ (by norm_num) (by norm_num) (by norm_num)

/-- World `0`'s priority: `tt > tf > ft > ff` (on a tie, the act that is `true` here).
Source: mandate Target 15 (ii)
Kind: D
Fidelity: n/a -/
def choice0 (𝒜 : Finset (Fin 2 → Bool)) : Fin 2 → Bool :=
  if tt ∈ 𝒜 then tt else if tf ∈ 𝒜 then tf else if ft ∈ 𝒜 then ft else ff

/-- World `1`'s priority: `tt > ft > tf > ff`.
Source: mandate Target 15 (ii)
Kind: D
Fidelity: n/a -/
def choice1 (𝒜 : Finset (Fin 2 → Bool)) : Fin 2 → Bool :=
  if tt ∈ 𝒜 then tt else if ft ∈ 𝒜 then ft else if tf ∈ 𝒜 then tf else ff

/-- **The behaviour of refutation (ii)**: on a tie, the act that is `true` at the current world.
Source: mandate Target 15 (ii)
Kind: D
Fidelity: n/a (an instance of MM Definition 3.3's `B_ω`) -/
def B2 (ω : Fin 2) (𝒜 : Finset (Fin 2 → Bool)) : Fin 2 → Bool :=
  if ω = 0 then choice0 𝒜 else choice1 𝒜

/-- **The behaviour of refutation (iii)**: the tie broken the other way at each world
(`B3 ω = B2 (ω + 1)`).
Source: mandate Target 15 (iii)
Kind: D
Fidelity: n/a (an instance of MM Definition 3.3's `B_ω`) -/
def B3 (ω : Fin 2) (𝒜 : Finset (Fin 2 → Bool)) : Fin 2 → Bool := B2 (ω + 1) 𝒜

/-- `B2` at world `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B2_zero (𝒜 : Finset (Fin 2 → Bool)) : B2 0 𝒜 = choice0 𝒜 := by simp [B2]

/-- `B2` at world `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B2_one (𝒜 : Finset (Fin 2 → Bool)) : B2 1 𝒜 = choice1 𝒜 := by simp [B2]

/-- `B3` at world `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B3_zero (𝒜 : Finset (Fin 2 → Bool)) : B3 0 𝒜 = choice1 𝒜 := by simp [B3, B2]

/-- `B3` at world `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B3_one (𝒜 : Finset (Fin 2 → Bool)) : B3 1 𝒜 = choice0 𝒜 := by simp [B3, B2]

/-- The agent's expected utility on `G2` is the number of `true`s over two.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_agentEU (ω : Fin 2) (a : Fin 2 → Bool) :
    G2.agentEU ω a = (uB (a 0) + uB (a 1)) / 2 := by
  simp [GFrame.agentEU, G2, E, Fin.sum_univ_two, half]; ring

/-- The type cell of every world of `G2` is everything.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_tcell (ω : Fin 2) : tcell G2 ω = univ := by
  ext w; simp [tcell, G2]

/-- Clarity holds on `G2` (vacuously).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_clarity : Clarity G2 := by
  intro ω ω' h
  rw [G2_tcell] at h
  exact absurd (mem_univ ω') h

/-- Richness holds on `G2` (all acts admissible).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_richness : Richness G2 := fun _ _ _ _ _ => mem_univ _

/-- Constant acts hold on `G2` (`tt` and `ff`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_constantActs : ConstantActs G2 :=
  ⟨true, false, by simp [G2, uB], mem_univ _, mem_univ _⟩

/-- A nonempty menu missing `tt`, `tf`, `ft` contains `ff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ff_mem_of {𝒜 : Finset (Fin 2 → Bool)} (hne : 𝒜.Nonempty) (h1 : tt ∉ 𝒜) (h2 : tf ∉ 𝒜)
    (h3 : ft ∉ 𝒜) : ff ∈ 𝒜 := by
  obtain ⟨a, ha⟩ := hne
  rcases act_cases a with rfl | rfl | rfl | rfl
  · exact absurd ha h1
  · exact absurd ha h2
  · exact absurd ha h3
  · exact ha

/-- The four acts' agent values on `G2` compared with a chosen act: numeric closure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem opt_of_mem {𝒜 : Finset (Fin 2 → Bool)} (ω : Fin 2) (c : Fin 2 → Bool)
    (hc : c = tt ∨ (c = tf ∧ tt ∉ 𝒜) ∨ (c = ft ∧ tt ∉ 𝒜) ∨ (c = ff ∧ tt ∉ 𝒜 ∧ tf ∉ 𝒜 ∧ ft ∉ 𝒜)) :
    ∀ a ∈ 𝒜, G2.agentEU ω a ≤ G2.agentEU ω c := by
  intro a ha
  rcases act_cases a with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1, h2, h3⟩ <;>
    first
      | exact absurd ha ‹_›
      | (simp only [G2_agentEU, tt, tf, ft, ff, uB]; norm_num)

/-- `choice0` is an agent-optimal act of the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choice0_spec {𝒜 : Finset (Fin 2 → Bool)} (hne : 𝒜.Nonempty) (ω : Fin 2) :
    choice0 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, G2.agentEU ω a ≤ G2.agentEU ω (choice0 𝒜) := by
  by_cases h1 : tt ∈ 𝒜
  · rw [choice0, if_pos h1]
    exact ⟨h1, opt_of_mem ω tt (Or.inl rfl)⟩
  by_cases h2 : tf ∈ 𝒜
  · rw [choice0, if_neg h1, if_pos h2]
    exact ⟨h2, opt_of_mem ω tf (Or.inr (Or.inl ⟨rfl, h1⟩))⟩
  by_cases h3 : ft ∈ 𝒜
  · rw [choice0, if_neg h1, if_neg h2, if_pos h3]
    exact ⟨h3, opt_of_mem ω ft (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩)))⟩
  · rw [choice0, if_neg h1, if_neg h2, if_neg h3]
    exact ⟨ff_mem_of hne h1 h2 h3, opt_of_mem ω ff (Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2, h3⟩)))⟩

/-- `choice1` is an agent-optimal act of the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem choice1_spec {𝒜 : Finset (Fin 2 → Bool)} (hne : 𝒜.Nonempty) (ω : Fin 2) :
    choice1 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, G2.agentEU ω a ≤ G2.agentEU ω (choice1 𝒜) := by
  by_cases h1 : tt ∈ 𝒜
  · rw [choice1, if_pos h1]
    exact ⟨h1, opt_of_mem ω tt (Or.inl rfl)⟩
  by_cases h3 : ft ∈ 𝒜
  · rw [choice1, if_neg h1, if_pos h3]
    exact ⟨h3, opt_of_mem ω ft (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩)))⟩
  by_cases h2 : tf ∈ 𝒜
  · rw [choice1, if_neg h1, if_neg h3, if_pos h2]
    exact ⟨h2, opt_of_mem ω tf (Or.inr (Or.inl ⟨rfl, h1⟩))⟩
  · rw [choice1, if_neg h1, if_neg h3, if_neg h2]
    exact ⟨ff_mem_of hne h1 h2 h3, opt_of_mem ω ff (Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2, h3⟩)))⟩

/-- `B2` is a behaviour on `G2`.
Source: mandate Target 15 (ii)
Kind: L
Fidelity: n/a -/
theorem B2_isBehaviour : IsBehaviour G2 B2 := by
  intro ω 𝒜 _ hne
  fin_cases ω
  · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B2_zero]; exact choice0_spec hne 0
  · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B2_one]; exact choice1_spec hne 1

/-- `B3` is a behaviour on `G2`.
Source: mandate Target 15 (iii)
Kind: L
Fidelity: n/a -/
theorem B3_isBehaviour : IsBehaviour G2 B3 := by
  intro ω 𝒜 _ hne
  fin_cases ω
  · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B3_zero]; exact choice1_spec hne 0
  · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B3_one]; exact choice0_spec hne 1

/-- Agent ties on `G2` are equalities or the pair `{tf, ft}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tie_cases {ω : Fin 2} {a b : Fin 2 → Bool} (h : G2.agentEU ω a = G2.agentEU ω b) :
    a = b ∨ (a = tf ∧ b = ft) ∨ (a = ft ∧ b = tf) := by
  rcases act_cases a with rfl | rfl | rfl | rfl <;> rcases act_cases b with rfl | rfl | rfl | rfl <;>
    simp only [G2_agentEU, tt, tf, ft, ff, uB] at h <;> norm_num at h <;> simp

/-- The delegated value on `G2` with `π2` and `B2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem delegValue_G2_B2 (𝒜 : Finset (Fin 2 → Bool)) :
    delegValue π2 G2 B2 𝒜 = 2 / 3 * uB (choice0 𝒜 0) + 1 / 3 * uB (choice1 𝒜 1) := by
  simp [delegValue, Fin.sum_univ_two, B2_zero, B2_one, π2, G2]

/-- **Refutation (ii), the valuing.** `π2` values `B2` on every decision problem.
Source: mandate Target 15 (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem valuesB_π2_B2 : ValuesB π2 G2 B2 := by
  intro 𝒜 _ hne a ha
  rw [delegValue_G2_B2]
  by_cases h1 : tt ∈ 𝒜 <;> by_cases h2 : tf ∈ 𝒜 <;> by_cases h3 : ft ∈ 𝒜 <;>
    simp only [choice0, choice1, h1, h2, h3, if_true, if_false] <;>
    rcases act_cases a with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd ha ‹_›
      | (simp only [E, Fin.sum_univ_two, Function.comp, G2, tt, tf, ft, ff, uB, π2]; norm_num)

/-- **Refutation (ii), stochastic choice (V-version).** Every act tied with a chosen act is chosen
at some `π2`-positive world of the same (unique) type.
Source: mandate Target 15 (ii); MM App. D l. 417
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem stochasticChoiceV_π2_B2 : StochasticChoiceV G2 π2 B2 := by
  intro 𝒜 _ a ha b hb ω htie hB
  have hpos : ∀ ω' : Fin 2, 0 < π2 ω' := by
    intro ω'; fin_cases ω' <;> norm_num [π2]
  rcases tie_cases htie with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ω, hpos ω, by rw [G2_tcell]; exact mem_univ _, hB⟩
  · -- `tf` chosen, so `tt ∉ 𝒜`; world `1` picks `ft`
    have h1 : tt ∉ 𝒜 := by
      intro h1
      fin_cases ω
      · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B2_zero, choice0, if_pos h1] at hB
        exact absurd (congrFun hB 1) (by simp [tt, tf])
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B2_one, choice1, if_pos h1] at hB
        exact absurd (congrFun hB 1) (by simp [tt, tf])
    refine ⟨1, hpos 1, by rw [G2_tcell]; exact mem_univ _, ?_⟩
    rw [B2_one]; simp [choice1, h1, hb]
  · have h1 : tt ∉ 𝒜 := by
      intro h1
      fin_cases ω
      · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B2_zero, choice0, if_pos h1] at hB
        exact absurd (congrFun hB 0) (by simp [tt, ft])
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B2_one, choice1, if_pos h1] at hB
        exact absurd (congrFun hB 0) (by simp [tt, ft])
    refine ⟨0, hpos 0, by rw [G2_tcell]; exact mem_univ _, ?_⟩
    rw [B2_zero]; simp [choice0, h1, hb]

/-- On `G2` the printed (`u`) and intended (`V_ω`) stochastic-choice conditions coincide.
Source: none: infrastructure (`V_ω = u`)
Kind: L
Fidelity: n/a -/
theorem stochasticChoiceU_iff_V_G2 (π : Fin 2 → ℝ) (B : Fin 2 → Finset (Fin 2 → Bool) → (Fin 2 → Bool)) :
    StochasticChoiceU G2 π B ↔ StochasticChoiceV G2 π B := Iff.rfl

/-- **Refutation (ii), strict agreement fails.** `E_π(u(tf)) = 2/3 > 1/3 = E_π(u(ft))` on the one
cell, while the agent ties (`1/2 = 1/2`).
Source: mandate Target 15 (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_strictAgree_π2 : ¬ StrictAgree π2 G2 := by
  intro h
  have := h tf (mem_univ _) ft (mem_univ _) 0 (by rw [G2_tcell]; norm_num [mass, Fin.sum_univ_two, π2])
    (by simp only [cellEU]; rw [G2_tcell]; norm_num [Fin.sum_univ_two, π2, uB, tf, ft, G2])
  simp only [G2_agentEU, tf, ft, uB] at this
  norm_num at this

/-- **MM Theorem 3.4 (⟹) as printed is false.** On the two-world frame `G2` with
`π = (2/3, 1/3)`: the behaviour `B2` is valued, satisfies stochastic choice (in both the printed
`u` and the intended `V` form — on `G2` the two coincide, `V = u`, so the `u`-form conjunct is
not independent evidence about the printed form), the frame is clear, rich and has constant
acts — yet strict conditional preference agreement fails. The frame has a single type cell, so
clarity is vacuous and conditional preference is unconditional preference: this refutes the
one-type instance of the printed theorem, which suffices. The printed proof's "we can run the
same argument" (l. 447) is where it breaks: stochastic choice supplies a world choosing the other
tied act, but that world need not be where the principal's conditional preference is tested.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97,
App. D l. 421–447 ("Then `π` values `(P, V)` if and only if …"); reading: MM's `B_ω` may depend on
`ω` within a type cell (Definition 3.3), ATTRIBUTION-UNVETTED; surviving neighbour:
`typeMeasurable_valuesB_iff_strictAgree`; items 083, 085
Kind: N+
Fidelity: exact (refutes the printed statement under the literal reading)
Hyps: (a) none -/
theorem mm34_forward_refuted :
    IsBehaviour G2 B2 ∧ ValuesB π2 G2 B2 ∧ StochasticChoiceU G2 π2 B2 ∧
    StochasticChoiceV G2 π2 B2 ∧ Clarity G2 ∧ Richness G2 ∧ ConstantActs G2 ∧
    ¬ StrictAgree π2 G2 :=
  ⟨B2_isBehaviour, valuesB_π2_B2, stochasticChoiceV_π2_B2, stochasticChoiceV_π2_B2,
    G2_clarity, G2_richness, G2_constantActs, not_strictAgree_π2⟩

/-- **Refutation (iii), strict agreement holds** when the agent is the principal's twin.
Source: mandate Target 15 (iii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem strictAgree_half_G2 : StrictAgree half G2 := by
  intro a _ b _ ω _ hlt
  simp only [cellEU] at hlt
  rw [G2_tcell] at hlt
  simp only [G2, Fin.sum_univ_two, half] at hlt
  simp only [G2_agentEU]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hlt
  linarith

/-- **Refutation (iii), stochastic choice for `B3`.**
Source: mandate Target 15 (iii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem stochasticChoiceV_half_B3 : StochasticChoiceV G2 half B3 := by
  intro 𝒜 _ a ha b hb ω htie hB
  have hpos : ∀ ω' : Fin 2, 0 < half ω' := by
    intro ω'; fin_cases ω' <;> norm_num [half]
  rcases tie_cases htie with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ω, hpos ω, by rw [G2_tcell]; exact mem_univ _, hB⟩
  · have h1 : tt ∉ 𝒜 := by
      intro h1
      fin_cases ω
      · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B3_zero, choice1, if_pos h1] at hB
        exact absurd (congrFun hB 1) (by simp [tt, tf])
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B3_one, choice0, if_pos h1] at hB
        exact absurd (congrFun hB 1) (by simp [tt, tf])
    refine ⟨0, hpos 0, by rw [G2_tcell]; exact mem_univ _, ?_⟩
    rw [B3_zero]; simp [choice1, h1, hb]
  · have h1 : tt ∉ 𝒜 := by
      intro h1
      fin_cases ω
      · rw [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, B3_zero, choice1, if_pos h1] at hB
        exact absurd (congrFun hB 0) (by simp [tt, ft])
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, B3_one, choice0, if_pos h1] at hB
        exact absurd (congrFun hB 0) (by simp [tt, ft])
    refine ⟨1, hpos 1, by rw [G2_tcell]; exact mem_univ _, ?_⟩
    rw [B3_one]; simp [choice0, h1, hb]

/-- **Refutation (iii), valuing fails**: on `{tf, ft}` the adversarial tie-break delivers `0`,
while `tf` is worth `1/2`.
Source: mandate Target 15 (iii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_valuesB_half_B3 : ¬ ValuesB half G2 B3 := by
  intro h
  have h1 : tt ∉ ({tf, ft} : Finset (Fin 2 → Bool)) := by
    simp only [mem_insert, mem_singleton, tt, tf, ft]; decide
  have hb0 : B3 0 {tf, ft} = ft := by
    rw [B3_zero, choice1, if_neg h1, if_pos (mem_insert_of_mem (mem_singleton_self _))]
  have hb1 : B3 1 {tf, ft} = tf := by
    rw [B3_one, choice0, if_neg h1, if_pos (mem_insert_self _ _)]
  have := h {tf, ft} (subset_univ _) (insert_nonempty _ _) tf (mem_insert_self _ _)
  simp only [delegValue, Fin.sum_univ_two] at this
  rw [hb0, hb1] at this
  simp only [E, Function.comp, G2, half, tf, ft, uB, Fin.sum_univ_two] at this
  norm_num at this

/-- **MM Theorem 3.4 (⟸) as printed is false — twin version (degenerate).** On `G2` with
`π = (1/2, 1/2)`: strict agreement, stochastic choice (both forms), clarity, richness and
constant acts hold, yet the behaviour `B3` is not valued. Graded **N−** (audit r1 B2(b)): the
agent is the principal's twin (`Pag ω = half = π`, `V = u`), so strict agreement is the identity
of two identical preference orders and only the tie-break does the work. The non-twin witness is
`mm34_backward_refuted` (`MM/Refute3.lean`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97,
App. D l. 421 (the "if" direction, never proved in App. D); reading as in
`mm34_forward_refuted`; surviving neighbour `typeMeasurable_valuesB_iff_strictAgree`; item 086
Kind: N-
Fidelity: exact (refutes the printed statement under the literal reading)
Hyps: (a) none -/
theorem mm34_backward_refuted_twin :
    IsBehaviour G2 B3 ∧ StrictAgree half G2 ∧ StochasticChoiceU G2 half B3 ∧
    StochasticChoiceV G2 half B3 ∧ Clarity G2 ∧ Richness G2 ∧ ConstantActs G2 ∧
    ¬ ValuesB half G2 B3 :=
  ⟨B3_isBehaviour, strictAgree_half_G2, stochasticChoiceV_half_B3, stochasticChoiceV_half_B3,
    G2_clarity, G2_richness, G2_constantActs, not_valuesB_half_B3⟩

/-! ## Stochastic choice presupposes a world-indexed behaviour (audit r1 N9/N10) -/

/-- `tf ≠ ft`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tf_ne_ft : tf ≠ ft := by
  intro h
  have := congrFun h 0
  simp [tf, ft] at this

/-- The agent ties between `tf` and `ft` at every world of `G2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem G2_tie_tf_ft (ω : Fin 2) : G2.agentEU ω tf = G2.agentEU ω ft := by
  simp [G2_agentEU, tf, ft, uB]

/-- **MM's stochastic-choice postulate is unsatisfiable by type-measurable behaviours on `G2`**,
for every `π` (`V`-form; the `u`-form is definitionally the same on `G2`,
`no_typeMeasurable_stochasticChoiceU_G2`). So the reading of Theorem 3.4 on which `B` is a
function of the type is inconsistent with Appendix D's own hypothesis: the postulate presupposes
that `B_ω` varies within a type cell, which is the literal reading the refutations use. (Adopted
from the round-1 adversarial audit's probe `Readings.lean`.)
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 417
(stochastic choice: "there exists `ω′` with `π(ω′) > 0` such that `P_ω′ = P_ω` and `V_ω′ = V_ω`,
but `B_ω′(A) = b`"); audit r1 (adversarial) N9, (fidelity) N10
Kind: P
Fidelity: exact (on the refuting frame)
Hyps: (a) none -/
theorem no_typeMeasurable_stochasticChoice_G2 (π : Fin 2 → ℝ)
    (B : Fin 2 → Finset (Fin 2 → Bool) → (Fin 2 → Bool))
    (hB : IsBehaviour G2 B) (htm : TypeMeasurable G2 B) : ¬ StochasticChoiceV G2 π B := by
  intro hsc
  have hsub : ({tf, ft} : Finset (Fin 2 → Bool)) ⊆ G2.A := subset_univ _
  obtain ⟨hmem, _⟩ := hB 0 {tf, ft} hsub (insert_nonempty _ _)
  rcases mem_insert.1 hmem with h0 | h0
  · obtain ⟨ω', _, hcell, hω'⟩ := hsc {tf, ft} hsub tf (mem_insert_self _ _) ft
      (mem_insert_of_mem (mem_singleton_self _)) 0 (G2_tie_tf_ft 0) h0
    have := htm 0 ω' {tf, ft} hcell
    rw [h0, hω'] at this
    exact tf_ne_ft this
  · rw [mem_singleton] at h0
    obtain ⟨ω', _, hcell, hω'⟩ := hsc {tf, ft} hsub ft
      (mem_insert_of_mem (mem_singleton_self _)) tf (mem_insert_self _ _) 0 (G2_tie_tf_ft 0).symm h0
    have := htm 0 ω' {tf, ft} hcell
    rw [h0, hω'] at this
    exact tf_ne_ft this.symm

/-- The same for the printed `u`-form.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 417
Kind: L
Fidelity: n/a -/
theorem no_typeMeasurable_stochasticChoiceU_G2 (π : Fin 2 → ℝ)
    (B : Fin 2 → Finset (Fin 2 → Bool) → (Fin 2 → Bool))
    (hB : IsBehaviour G2 B) (htm : TypeMeasurable G2 B) : ¬ StochasticChoiceU G2 π B :=
  no_typeMeasurable_stochasticChoice_G2 π B hB htm

/-! ## (vi) The Rain example -/

/-- The third coordinate of a four-vector (not in the default simp set).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_two (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := rfl

/-- The fourth coordinate of a four-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_three (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := rfl

/-- The Rain frame's worlds: `0 = (Rain, ω)`, `1 = (¬Rain, ω)`, `2 = (Rain, ω')`,
`3 = (¬Rain, ω')`. The principal: `π = ½ δ₀ + ½ δ₃` ("`π(Rain | [P = P_ω]) = 1`,
`π(Rain | [P = P_ω']) = 0`").
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: D
Fidelity: exact -/
def rainπ : Fin 4 → ℝ := ![1 / 2, 0, 0, 1 / 2]

/-- `rainπ` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rainπ_mem : rainπ ∈ stdSimplex ℝ (Fin 4) := by
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [rainπ]
  · norm_num [Fin.sum_univ_four, rainπ, vec4_two, vec4_three]

/-- Type `ω`'s beliefs: Rain with probability `6/10`, concentrated on its own cell `{0, 1}`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: D
Fidelity: exact -/
def rainPω : Fin 4 → ℝ := ![6 / 10, 4 / 10, 0, 0]

/-- Type `ω'`'s beliefs: Rain with probability `4/10`, concentrated on its cell `{2, 3}`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: D
Fidelity: exact -/
def rainPω' : Fin 4 → ℝ := ![0, 0, 4 / 10, 6 / 10]

/-- The bet `g_x`: `1 − x` if Rain, `−x` otherwise (consequences are money, `u = id`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: D
Fidelity: exact -/
def bet (x : ℝ) : Fin 4 → ℝ := ![1 - x, -x, 1 - x, -x]

/-- The Rain generalized frame for the bet `g_x`: `A = {g_x, 0}`, `V = u = id`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: D
Fidelity: exact (the admissible acts are the two acts of the one decision problem) -/
def rainG (x : ℝ) : GFrame (Fin 4) ℝ where
  u := id
  Pag := ![rainPω, rainPω, rainPω', rainPω']
  Pag_mem := by
    intro w
    fin_cases w
    · exact ⟨fun v => by fin_cases v <;> norm_num [rainPω], by norm_num [Fin.sum_univ_four, rainPω, vec4_two, vec4_three]⟩
    · exact ⟨fun v => by fin_cases v <;> norm_num [rainPω], by norm_num [Fin.sum_univ_four, rainPω, vec4_two, vec4_three]⟩
    · exact ⟨fun v => by fin_cases v <;> norm_num [rainPω'], by norm_num [Fin.sum_univ_four, rainPω', vec4_two, vec4_three]⟩
    · exact ⟨fun v => by fin_cases v <;> norm_num [rainPω'], by norm_num [Fin.sum_univ_four, rainPω', vec4_two, vec4_three]⟩
  V := fun _ => id
  A := {bet x, fun _ => 0}

/-- The agent's expected utilities of the bet at the two types.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rain_agentEU (x : ℝ) :
    (rainG x).agentEU 0 (bet x) = 6 / 10 - x ∧ (rainG x).agentEU 3 (bet x) = 4 / 10 - x ∧
    (rainG x).agentEU 0 (fun _ => 0) = 0 ∧ (rainG x).agentEU 3 (fun _ => 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [GFrame.agentEU, rainG, E, Fin.sum_univ_four, rainPω, rainPω', bet, vec4_two, vec4_three] <;>
    ring

/-- **The Rain example, valuing on the bet.** For every stake `x ∈ [0, 1]` and every behaviour
(any tie-break), the principal values delegating the menus `⊆ {g_x, 0}`:
`E_π(u(B(𝒜))) ≥ max(E_π(g_x), 0)` — although (below) she conditionally disagrees with the agent.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
("the principal should delegate in this situation no matter what `x` is"); item 085
Kind: N+
Fidelity: exact
Hyps: (a) `0 ≤ x ≤ 1`, `IsBehaviour` -/
theorem rain_valuesB {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {B : Fin 4 → Finset (Fin 4 → ℝ) → (Fin 4 → ℝ)} (hB : IsBehaviour (rainG x) B) :
    ValuesB rainπ (rainG x) B := by
  obtain ⟨e0, e3, z0, z3⟩ := rain_agentEU x
  intro 𝒜 hsub hne a ha
  have hA : ∀ b ∈ 𝒜, b = bet x ∨ b = fun _ => 0 := by
    intro b hb
    have := hsub hb
    simp only [rainG, mem_insert, mem_singleton] at this
    exact this
  obtain ⟨hm0, ho0⟩ := hB 0 𝒜 hsub hne
  obtain ⟨hm3, ho3⟩ := hB 3 𝒜 hsub hne
  have hdel : delegValue rainπ (rainG x) B 𝒜 = 1 / 2 * B 0 𝒜 0 + 1 / 2 * B 3 𝒜 3 := by
    simp [delegValue, Fin.sum_univ_four, rainπ, rainG, vec4_two, vec4_three]
  have hEa : E rainπ ((rainG x).u ∘ a) = 1 / 2 * a 0 + 1 / 2 * a 3 := by
    simp [E, Fin.sum_univ_four, rainπ, rainG, vec4_two, vec4_three]
  rw [hdel, hEa]
  have hb0 : bet x 0 = 1 - x := rfl
  have hb3 : bet x 3 = -x := rfl
  -- the agent's choices are optimal at each type
  rcases hA _ hm0 with h0 | h0 <;> rcases hA _ hm3 with h3 | h3
  · -- both accept: `x ≤ 4/10` if `0` is on the menu
    rcases hA a ha with rfl | rfl
    · rw [h0, h3]
    · have h4 := ho3 _ ha
      rw [h3, e3, z3] at h4
      rw [h0, h3, hb0, hb3]
      simp only
      linarith
  · -- type `ω` accepts, type `ω'` rejects
    rcases hA a ha with rfl | rfl
    · rw [h0, h3, hb0, hb3]; simp only; linarith
    · rw [h0, h3, hb0]; simp only; linarith
  · -- type `ω` rejects but type `ω'` accepts: impossible
    exfalso
    have h1 := ho0 (bet x) (by rw [← h3]; exact hm3)
    have h2 := ho3 (fun _ => 0) (by rw [← h0]; exact hm0)
    rw [h0, e0, z0] at h1
    rw [h3, e3, z3] at h2
    linarith
  · -- both reject: `x ≥ 6/10`
    rcases hA a ha with rfl | rfl
    · have h1 := ho0 _ ha
      rw [h0, e0, z0] at h1
      rw [h0, h3, hb0, hb3]
      simp only
      linarith
    · rw [h0, h3]

/-- The Rain frame is clear: each type's beliefs live on its own cell.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
Kind: L
Fidelity: n/a -/
theorem rain_clarity (x : ℝ) : Clarity (rainG x) := by
  intro ω ω' h
  simp only [tcell, mem_filter, mem_univ, true_and, not_and, rainG] at h
  fin_cases ω <;> fin_cases ω' <;> simp [rainG, rainPω, rainPω', vec4_two, vec4_three] at h ⊢

/-- **The Rain example, strict agreement fails at `x = 9/10`**: on the cell `[ω] = {0, 1}`,
`E_π(u(g_{0.9}) | [ω]) = 1/10 > 0 = E_π(u(0) | [ω])` (the principal accepts), while
`E_ω(g_{0.9}) = 6/10 − 9/10 < 0 = E_ω(0)` (the agent rejects). Richness fails on
`A = {g_x, 0}`, which is why valuing and disagreement coexist.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 105
("If `x = .9`, then conditional on `[P = P_ω]`, the principal will want to accept the bet, while
the agent will reject the bet"); item 085
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem rain_not_strictAgree : ¬ StrictAgree rainπ (rainG (9 / 10)) := by
  intro h
  obtain ⟨e0, _, z0, _⟩ := rain_agentEU (9 / 10)
  have hcell : tcell (rainG (9 / 10)) 0 = {0, 1} := by
    ext w
    simp only [tcell, mem_filter, mem_univ, true_and, rainG, mem_insert, mem_singleton]
    fin_cases w <;> simp [rainPω, rainPω']
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have := h (bet (9 / 10)) (by simp [rainG]) (fun _ => 0) (by simp [rainG]) 0
    (by rw [hcell]; norm_num [mass, sum_pair h01, rainπ])
    (by simp only [cellEU, hcell, sum_pair h01]; norm_num [rainπ, rainG, bet, vec4_two, vec4_three])
  rw [e0, z0] at this
  norm_num at this

/-- Richness fails for the Rain frame at `x = 9/10` (the splice `g` on `{0}`, `0` elsewhere is
neither admissible act).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 103
("when we limit the scope of decisions")
Kind: L
Fidelity: n/a -/
theorem rain_not_richness : ¬ Richness (rainG (9 / 10)) := by
  intro h
  have := h (bet (9 / 10)) (by simp [rainG]) (fun _ => 0) (by simp [rainG]) {0}
  simp only [rainG, mem_insert, mem_singleton] at this
  rcases this with e | e
  · have := congrFun e 1; norm_num [splice, bet] at this
  · have := congrFun e 0; norm_num [splice, bet] at this

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM
