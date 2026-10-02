import Cleanroom.Lit.LitShutdownPrefs.SIS

/-!
# Witnesses for the First Theorem, and Thorstad's Monotonicity restatement refuted (Targets 3, 4)

* `witness f g h …` — the state over `R := Fin 2` (`0` = unpressed rest, `1` = pressed rest) with
  `P₀ = dirac 1`, `U₀ = dirac 0`, for any `0 ≤ f < g < h ≤ 1`.
* **N+ (averse)**: the EU relation with `u (a, unpressed) = 1`, `u (a, pressed) = 0` satisfies all
  four hypotheses of `first_theorem_averse`, has `U a ≻ P a` for every `a`, and the conclusion
  `ShutdownAverse` is checked directly by arithmetic (`1 − g < 1 − f`), not through the theorem.
* **N+ (seeking)**: the same with the values swapped.
* **Non-degeneracy (gap)** (`witness_gap`, over `R := Fin 3`): the two-criterion dominance
  relation `domLe crit0 crit1` (criteria `[r = 0]`, `[r = 1]`) satisfies the four hypotheses, has
  genuine strict preferences (`(a, 0) ≻ (a, 2)`), a *gap* between every `U a` and `P a`, and the
  three actions pairwise incomparable (criterion vectors `(1 − prob a, prob a)`); so neither
  conclusion holds for a non-trivial reason. This is the escape the Second Theorem closes. Over
  `Fin 2` the same construction collapses (`witness_gap_fin2`, N−): the two label-blind criteria
  sum to `1`, the relation is the equivalence "equal unpressed mass" and has no strict
  preferences at all (`domLe_fin2_lt_empty`) — audit round 1, fidelity B1 / adversarial B4.
* **Thorstad refuted** (`thorstad_monotonicity_restatement_refuted`): with Better Chances replaced
  by his weak one-directional Monotonicity, the First Theorem is false. Counter-model: `le X Y :⇔
  posInd (m Y) ≤ posInd (m X)` where `m X` is the unpressed mass and `posInd s = [s > 0]`. It is
  transitive, complete, satisfies IABM, IBILsub and Monotonicity, has `U a ≻ P a`, but
  `act Prevent ~ act Leave` because both have positive unpressed mass (`1 − f`, `1 − g > 0`, and
  `g < h ≤ 1` forces `g < 1`). The mandate's three-level class function is not needed: the
  two-level one refutes for every admissible `(f, g, h)`, including `f = 0`.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace SIS

open Lottery Weak

/-- The witness shutdown-influencing state over `Fin 2` (`0` unpressed, `1` pressed): the rest of
the trajectory is just the button status.
Source: [[lit-shutdown-prefs-mandate]] Target 3 (Witness N+)
Kind: N+
Fidelity: n/a -/
noncomputable def witness (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1) :
    SIS (Fin 2) where
  f := f
  g := g
  h := h
  f_nonneg := hf
  f_lt_g := hfg
  g_lt_h := hgh
  h_le_one := hh
  P₀ := dirac 1
  U₀ := dirac 0

/-- Utility `1` on unpressed, `0` on pressed, blind to the action label.
Source: [[lit-shutdown-prefs-mandate]] Target 3
Kind: N+ -/
def uUnpressed : Act × Fin 2 → ℝ := fun x => if x.2 = 0 then 1 else 0

/-- Utility `0` on unpressed, `1` on pressed, blind to the action label.
Source: [[lit-shutdown-prefs-mandate]] Target 3
Kind: N+ -/
def uPressed : Act × Fin 2 → ℝ := fun x => if x.2 = 0 then 0 else 1

section witness

variable (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1)

/-- In the witness, `P a = dirac (a, pressed)`.
Source: none: infrastructure
Kind: L -/
theorem witness_P (a : Act) : (witness f g h hf hfg hgh hh).P a = dirac (a, 1) := by
  simp [P, witness, map_dirac]

/-- In the witness, `U a = dirac (a, unpressed)`.
Source: none: infrastructure
Kind: L -/
theorem witness_U (a : Act) : (witness f g h hf hfg hgh hh).U a = dirac (a, 0) := by
  simp [U, witness, map_dirac]

/-- The expectation of an action lottery in the witness.
Source: none: infrastructure
Kind: L -/
theorem witness_expect_act (u : Act × Fin 2 → ℝ) (a : Act) :
    ((witness f g h hf hfg hgh hh).act a).expect u =
      (witness f g h hf hfg hgh hh).prob a * u (a, 1) +
        (1 - (witness f g h hf hfg hgh hh).prob a) * u (a, 0) := by
  simp [act, witness_P, witness_U]

/-- **N+ witness, shutdown-averse clause.** For the EU relation with `u = uUnpressed`: all four
hypotheses of the First Theorem hold, `U a ≻ P a` for every `a`, and the state is shutdown-averse
— the last checked directly (`1 − g < 1 − f`, `1 − h < 1 − f`), independently of the theorem.
Source: [[lit-shutdown-prefs-mandate]] Target 3 (Witness N+)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem witness_averse :
    Weak.Transitive (euLe uUnpressed) ∧ IABM (euLe uUnpressed) ∧ IBILsub (euLe uUnpressed) ∧
      StrictMonotone (euLe uUnpressed) ∧
      (∀ a, lt (euLe uUnpressed) ((witness f g h hf hfg hgh hh).U a)
        ((witness f g h hf hfg hgh hh).P a)) ∧
      (witness f g h hf hfg hgh hh).ShutdownAverse (euLe uUnpressed) := by
  refine ⟨euLe_transitive _, (euLe_iabm_iff _).mpr fun _ _ _ => rfl, euLe_ibilSub _,
    euLe_strictMonotone _, fun a => ?_, ?_, ?_⟩
  · rw [euLe_lt_iff, witness_P, witness_U]; simp [uUnpressed]
  · rw [euLe_lt_iff, witness_expect_act, witness_expect_act]
    simp [uUnpressed, witness, prob]; linarith
  · rw [euLe_lt_iff, witness_expect_act, witness_expect_act]
    simp [uUnpressed, witness, prob]; linarith

/-- **N+ witness, shutdown-seeking clause.** With `u = uPressed`: all four hypotheses, `P a ≻ U a`
for every `a`, and the state is shutdown-seeking, checked directly (`g < h`, `f < h`).
Source: [[lit-shutdown-prefs-mandate]] Target 3 (second witness)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem witness_seeking :
    Weak.Transitive (euLe uPressed) ∧ IABM (euLe uPressed) ∧ IBILsub (euLe uPressed) ∧
      StrictMonotone (euLe uPressed) ∧
      (∀ a, lt (euLe uPressed) ((witness f g h hf hfg hgh hh).P a)
        ((witness f g h hf hfg hgh hh).U a)) ∧
      (witness f g h hf hfg hgh hh).ShutdownSeeking (euLe uPressed) := by
  refine ⟨euLe_transitive _, (euLe_iabm_iff _).mpr fun _ _ _ => rfl, euLe_ibilSub _,
    euLe_strictMonotone _, fun a => ?_, ?_, ?_⟩
  · rw [euLe_lt_iff, witness_P, witness_U]; simp [uPressed]
  · rw [euLe_lt_iff, witness_expect_act, witness_expect_act]
    simp [uPressed, witness, prob]; linarith
  · rw [euLe_lt_iff, witness_expect_act, witness_expect_act]
    simp [uPressed, witness, prob]; linarith

end witness

/-! ## Non-degeneracy: a gap escapes both conclusions -/

/-- The two-criterion dominance relation: `X ≽ Y` iff `X` has at least the expected `u` *and* at
least the expected `w`. Incomplete when the criteria disagree.
Source: [[lit-shutdown-prefs-mandate]] Target 3 (non-degeneracy check)
Kind: D
Fidelity: n/a -/
def domLe {T : Type} (u w : T → ℝ) (X Y : Lottery T) : Prop := euLe u X Y ∧ euLe w X Y

section dom

variable {T : Type} (u w : T → ℝ)

/-- Dominance is transitive.
Source: none: infrastructure
Kind: L -/
theorem domLe_transitive : Weak.Transitive (domLe u w) := fun _ _ _ h1 h2 =>
  ⟨euLe_transitive u _ _ _ h1.1 h2.1, euLe_transitive w _ _ _ h1.2 h2.2⟩

/-- Dominance satisfies IBIL (substitution form).
Source: none: infrastructure
Kind: L -/
theorem domLe_ibilSub : IBILsub (domLe u w) := by
  intro X Y Z p hp h
  have h1 : indiff (euLe u) X Y := ⟨h.1.1, h.2.1⟩
  have h2 : indiff (euLe w) X Y := ⟨h.1.2, h.2.2⟩
  have e1 := euLe_ibilSub u X Y Z p hp h1
  have e2 := euLe_ibilSub w X Y Z p hp h2
  exact ⟨⟨e1.1, e2.1⟩, ⟨e1.2, e2.2⟩⟩

/-- Dominance satisfies Strict Monotonicity.
Source: none: infrastructure
Kind: L -/
theorem domLe_strictMonotone : StrictMonotone (domLe u w) := by
  intro X Y p q hp hq hpq ⟨⟨h1, h2⟩, h3⟩
  simp only [euLe] at h1 h2
  simp only [domLe, euLe] at h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (mix q hq X Y).expect u ≤ (mix p hp X Y).expect u
    rw [expect_mix, expect_mix]; nlinarith
  · show (mix q hq X Y).expect w ≤ (mix p hp X Y).expect w
    rw [expect_mix, expect_mix]; nlinarith
  · rintro ⟨h4, h5⟩
    simp only [euLe, expect_mix] at h4 h5
    apply h3
    constructor <;> nlinarith

/-- Dominance satisfies IABM when both criteria are label-blind.
Source: none: infrastructure
Kind: L -/
theorem domLe_iabm {Act R : Type} (v v' : Act × R → ℝ) (hv : ∀ a a' r, v (a, r) = v (a', r))
    (hv' : ∀ a a' r, v' (a, r) = v' (a', r)) : IABM (domLe v v') := by
  intro a a' r
  have e1 := (euLe_iabm_iff v).mpr hv a a' r
  have e2 := (euLe_iabm_iff v').mpr hv' a a' r
  exact ⟨⟨e1.1, e2.1⟩, ⟨e1.2, e2.2⟩⟩

end dom

section gap2

variable (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1)

/-- The two `Fin 2` criteria sum to `1` pointwise.
Source: audit round 1, fidelity B1 (probe `GapWitnessDegenerate.lean`)
Kind: L -/
theorem uUnpressed_add_uPressed (x : Act × Fin 2) : uUnpressed x + uPressed x = 1 := by
  unfold uUnpressed uPressed; split_ifs <;> norm_num

/-- Hence `E[uPressed] = 1 − E[uUnpressed]` for every lottery.
Source: audit round 1, fidelity B1
Kind: L -/
theorem expect_uPressed (X : Lottery (Act × Fin 2)) :
    X.expect uPressed = 1 - X.expect uUnpressed := by
  have h := X.expect_add uUnpressed uPressed
  have h2 : X.expect (fun x => uUnpressed x + uPressed x) = 1 := by
    rw [X.expect_congr (g₂ := fun _ => 1) (fun x _ => uUnpressed_add_uPressed x)]
    exact X.expect_const_one
  linarith

/-- Over `Fin 2` the dominance relation is the equivalence "equal unpressed mass".
Source: audit round 1, fidelity B1
Kind: L -/
theorem domLe_fin2_iff (X Y : Lottery (Act × Fin 2)) :
    domLe uUnpressed uPressed X Y ↔ X.expect uUnpressed = Y.expect uUnpressed := by
  unfold domLe euLe
  rw [expect_uPressed, expect_uPressed]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- **The `Fin 2` dominance relation has no strict preferences** — which is why `witness_gap_fin2`
is graded N−.
Source: audit round 1, fidelity B1 / adversarial B4
Kind: N− -/
theorem domLe_fin2_lt_empty (X Y : Lottery (Act × Fin 2)) :
    ¬ lt (domLe uUnpressed uPressed) X Y := by
  rintro ⟨h1, h2⟩
  rw [domLe_fin2_iff] at h1 h2
  exact h2 h1.symm

/-- **Joint consistency over `Fin 2` (degenerate)**: the dominance relation
`domLe uUnpressed uPressed` satisfies Transitivity, IABM, IBIL and Strict Monotonicity, has a
preferential *gap* between every `U a` and `P a`, and the witness state is neither shutdown-averse
nor shutdown-seeking. This shows the four conditions plus a gap are jointly satisfiable, but
**degenerately**: on `Fin 2` the two label-blind criteria sum to `1`, so the relation is the
equivalence "equal unpressed mass", its strict part is empty (`domLe_fin2_lt_empty`), Strict
Monotonicity holds vacuously and "neither averse nor seeking" holds because nothing is strictly
preferred to anything. The non-degenerate witness is `witness_gap` over `Fin 3`.
Source: [[lit-shutdown-prefs-mandate]] Target 3 ("the escape the Second Theorem closes"); audit
round 1, fidelity B1 / adversarial B4 (regraded)
Kind: N−
Fidelity: n/a
Hyps: (a) all -/
theorem witness_gap_fin2 :
    Weak.Transitive (domLe uUnpressed uPressed) ∧ IABM (domLe uUnpressed uPressed) ∧
      IBILsub (domLe uUnpressed uPressed) ∧ StrictMonotone (domLe uUnpressed uPressed) ∧
      (∀ a, gap (domLe uUnpressed uPressed) ((witness f g h hf hfg hgh hh).U a)
        ((witness f g h hf hfg hgh hh).P a)) ∧
      ¬ (witness f g h hf hfg hgh hh).ShutdownAverse (domLe uUnpressed uPressed) ∧
      ¬ (witness f g h hf hfg hgh hh).ShutdownSeeking (domLe uUnpressed uPressed) := by
  refine ⟨domLe_transitive _ _, domLe_iabm _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    domLe_ibilSub _ _, domLe_strictMonotone _ _, fun a => ?_, ?_, ?_⟩
  · rw [witness_P, witness_U]
    simp [gap, domLe, euLe, uUnpressed, uPressed]
  · rintro ⟨⟨hle, _⟩, _⟩
    have h2 : ((witness f g h hf hfg hgh hh).act .Leave).expect uPressed ≤
        ((witness f g h hf hfg hgh hh).act .Prevent).expect uPressed := hle.2
    rw [witness_expect_act, witness_expect_act] at h2
    simp [uPressed, witness, prob] at h2
    linarith
  · rintro ⟨⟨hle, _⟩, _⟩
    have h2 : ((witness f g h hf hfg hgh hh).act .Leave).expect uUnpressed ≤
        ((witness f g h hf hfg hgh hh).act .Cause).expect uUnpressed := hle.1
    rw [witness_expect_act, witness_expect_act] at h2
    simp [uUnpressed, witness, prob] at h2
    linarith

end gap2

/-! ## Non-degeneracy over `Fin 3`: a gap escapes both conclusions, with strict preferences -/

/-- The three-state witness (`0` unpressed rest, `1` pressed rest, `2` a third rest-trajectory that
neither criterion values) with `P₀ = dirac 1`, `U₀ = dirac 0`, for any `0 ≤ f < g < h ≤ 1`.
Source: audit round 1, fidelity B1 / adversarial B4 ("a genuine gap witness needs a third state")
Kind: N+
Fidelity: n/a -/
noncomputable def witness3 (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1) :
    SIS (Fin 3) where
  f := f
  g := g
  h := h
  f_nonneg := hf
  f_lt_g := hfg
  g_lt_h := hgh
  h_le_one := hh
  P₀ := dirac 1
  U₀ := dirac 0

/-- Criterion `[r = 0]` on `Act × Fin 3` (values the unpressed rest), label-blind.
Source: audit round 1, adversarial B4
Kind: N+ -/
def crit0 : Act × Fin 3 → ℝ := fun x => if x.2 = 0 then 1 else 0

/-- Criterion `[r = 1]` on `Act × Fin 3` (values the pressed rest), label-blind.
Source: audit round 1, adversarial B4
Kind: N+ -/
def crit1 : Act × Fin 3 → ℝ := fun x => if x.2 = 1 then 1 else 0

section gap3

variable (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1)

/-- In the three-state witness, `P a = dirac (a, 1)`.
Source: none: infrastructure
Kind: L -/
theorem witness3_P (a : Act) : (witness3 f g h hf hfg hgh hh).P a = dirac (a, 1) := by
  simp [P, witness3, map_dirac]

/-- In the three-state witness, `U a = dirac (a, 0)`.
Source: none: infrastructure
Kind: L -/
theorem witness3_U (a : Act) : (witness3 f g h hf hfg hgh hh).U a = dirac (a, 0) := by
  simp [U, witness3, map_dirac]

/-- The expectation of an action lottery in the three-state witness.
Source: none: infrastructure
Kind: L -/
theorem witness3_expect_act (u : Act × Fin 3 → ℝ) (a : Act) :
    ((witness3 f g h hf hfg hgh hh).act a).expect u =
      (witness3 f g h hf hfg hgh hh).prob a * u (a, 1) +
        (1 - (witness3 f g h hf hfg hgh hh).prob a) * u (a, 0) := by
  simp [act, witness3_P, witness3_U]

/-- Dominance between two actions of the three-state witness: `act a ≽ act b` iff the criterion
vectors `(1 − prob a, prob a)` and `(1 − prob b, prob b)` are ordered, i.e. iff `prob a = prob b`.
Source: none: infrastructure
Kind: L -/
theorem witness3_domLe_act_iff (a b : Act) :
    domLe crit0 crit1 ((witness3 f g h hf hfg hgh hh).act a) ((witness3 f g h hf hfg hgh hh).act b) ↔
      (witness3 f g h hf hfg hgh hh).prob a = (witness3 f g h hf hfg hgh hh).prob b := by
  simp only [domLe, euLe, witness3_expect_act]
  simp [crit0, crit1]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- **Non-degeneracy of the First Theorem's hypothesis package** (N+): over `Fin 3`, the
dominance relation `domLe crit0 crit1` satisfies Transitivity, IABM, IBIL and Strict Monotonicity;
it has genuine strict preferences (`(a, 0) ≻ (a, 2)` for every `a`); it has a preferential *gap*
between every `U a` (criteria `(1, 0)`) and `P a` (criteria `(0, 1)`); the three actions, with
criterion vectors `(1 − prob a, prob a)` and `f < g < h`, are pairwise incomparable; and the
witness state is neither shutdown-averse nor shutdown-seeking. So the antecedent
`∃ a, U a ≻ P a ∨ P a ≻ U a` of the First Theorem is not idle: it is exactly the gap-free case the
Second Theorem forces under Completeness, and here the escape is taken by a relation with real
strict preferences, not by an empty one.
Source: [[lit-shutdown-prefs-mandate]] Target 3 ("the escape the Second Theorem closes"); audit
round 1, fidelity B1 fix (ii) / adversarial B4 fix
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem witness_gap :
    Weak.Transitive (domLe crit0 crit1) ∧ IABM (domLe crit0 crit1) ∧
      IBILsub (domLe crit0 crit1) ∧ StrictMonotone (domLe crit0 crit1) ∧
      (∀ a : Act, lt (domLe crit0 crit1) (dirac (a, 0)) (dirac (a, 2))) ∧
      (∀ a, gap (domLe crit0 crit1) ((witness3 f g h hf hfg hgh hh).U a)
        ((witness3 f g h hf hfg hgh hh).P a)) ∧
      gap (domLe crit0 crit1) ((witness3 f g h hf hfg hgh hh).act .Prevent)
        ((witness3 f g h hf hfg hgh hh).act .Leave) ∧
      gap (domLe crit0 crit1) ((witness3 f g h hf hfg hgh hh).act .Prevent)
        ((witness3 f g h hf hfg hgh hh).act .Cause) ∧
      gap (domLe crit0 crit1) ((witness3 f g h hf hfg hgh hh).act .Leave)
        ((witness3 f g h hf hfg hgh hh).act .Cause) ∧
      ¬ (witness3 f g h hf hfg hgh hh).ShutdownAverse (domLe crit0 crit1) ∧
      ¬ (witness3 f g h hf hfg hgh hh).ShutdownSeeking (domLe crit0 crit1) := by
  have hgap : ∀ a b : Act, (witness3 f g h hf hfg hgh hh).prob a ≠ (witness3 f g h hf hfg hgh hh).prob b →
      gap (domLe crit0 crit1) ((witness3 f g h hf hfg hgh hh).act a)
        ((witness3 f g h hf hfg hgh hh).act b) := fun a b hne =>
    ⟨fun hle => hne ((witness3_domLe_act_iff f g h hf hfg hgh hh a b).mp hle),
      fun hle => hne (((witness3_domLe_act_iff f g h hf hfg hgh hh b a).mp hle).symm)⟩
  refine ⟨domLe_transitive _ _, domLe_iabm _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    domLe_ibilSub _ _, domLe_strictMonotone _ _, fun a => ?_, fun a => ?_,
    hgap _ _ (by simp [witness3, prob]; exact hfg.ne),
    hgap _ _ (by simp [witness3, prob]; exact (hfg.trans hgh).ne),
    hgap _ _ (by simp [witness3, prob]; exact hgh.ne), ?_, ?_⟩
  · simp [lt, domLe, euLe, crit0, crit1]
  · rw [witness3_P, witness3_U]
    simp [gap, domLe, euLe, crit0, crit1]
  · rintro ⟨⟨hle, _⟩, _⟩
    have := (witness3_domLe_act_iff f g h hf hfg hgh hh _ _).mp hle
    simp [witness3, prob] at this
    linarith
  · rintro ⟨⟨hle, _⟩, _⟩
    have := (witness3_domLe_act_iff f g h hf hfg hgh hh _ _).mp hle
    simp [witness3, prob] at this
    linarith

end gap3

/-! ## Thorstad's Monotonicity restatement, refuted -/

/-- The unpressed mass of a lottery over `Act × Fin 2`.
Source: [[lit-shutdown-prefs-mandate]] Target 4 (`m X`)
Kind: D -/
noncomputable def mUnp (X : Lottery (Act × Fin 2)) : ℝ := X.mass (fun x => x.2 = 0)

/-- The positivity indicator `[s > 0]` (the two-level class function).
Source: [[lit-shutdown-prefs-mandate]] Target 4 (`cls`, collapsed to two levels)
Kind: D -/
noncomputable def posInd (s : ℝ) : ℝ := if 0 < s then 1 else 0

/-- Thorstad's counter-model relation: `X ≽ Y :⇔ posInd (m Y) ≤ posInd (m X)`.
Source: [[lit-shutdown-prefs-mandate]] Target 4
Kind: D
Fidelity: n/a -/
noncomputable def clsLe (X Y : Lottery (Act × Fin 2)) : Prop := posInd (mUnp Y) ≤ posInd (mUnp X)

/-- `posInd a ≤ posInd b ↔ (0 < a → 0 < b)`.
Source: none: infrastructure
Kind: L -/
theorem posInd_le_iff (a b : ℝ) : posInd a ≤ posInd b ↔ (0 < a → 0 < b) := by
  unfold posInd
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

/-- Positivity of a mixture of nonnegative reals.
Source: none: infrastructure
Kind: L -/
theorem pos_mix_iff {x z p : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < p * x + (1 - p) * z ↔ (0 < p ∧ 0 < x) ∨ (p < 1 ∧ 0 < z) := by
  obtain ⟨hp0, hp1⟩ := hp
  have h1 : 0 ≤ p * x := mul_nonneg hp0 hx
  have h2 : 0 ≤ (1 - p) * z := mul_nonneg (by linarith) hz
  constructor
  · intro hpos
    by_contra hc
    push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have e1 : p * x = 0 := by
      rcases eq_or_lt_of_le hp0 with h' | h'
      · rw [← h', zero_mul]
      · have hx0 : x = 0 := le_antisymm (hc1 h') hx
        rw [hx0, mul_zero]
    have e2 : (1 - p) * z = 0 := by
      rcases eq_or_lt_of_le hp1 with h' | h'
      · rw [h', sub_self, zero_mul]
      · have hz0 : z = 0 := le_antisymm (hc2 h') hz
        rw [hz0, mul_zero]
    linarith
  · rintro (⟨hp', hx'⟩ | ⟨hp', hz'⟩)
    · have : 0 < p * x := mul_pos hp' hx'; linarith
    · have : 0 < (1 - p) * z := mul_pos (by linarith) hz'; linarith

/-- The unpressed mass of a mixture.
Source: none: infrastructure
Kind: L -/
theorem mUnp_mix (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (X Y : Lottery (Act × Fin 2)) :
    mUnp (mix p hp X Y) = p * mUnp X + (1 - p) * mUnp Y := by
  simp [mUnp, mass]

/-- The unpressed mass is nonnegative.
Source: none: infrastructure
Kind: L -/
theorem mUnp_nonneg (X : Lottery (Act × Fin 2)) : 0 ≤ mUnp X := X.mass_nonneg _

/-- The counter-model is transitive.
Source: none: infrastructure
Kind: L -/
theorem clsLe_transitive : Weak.Transitive clsLe := fun _ _ _ h1 h2 => le_trans h2 h1

/-- The counter-model is complete.
Source: none: infrastructure
Kind: L -/
theorem clsLe_complete : Complete clsLe := fun _ _ => le_total _ _

/-- The counter-model satisfies IABM (the label is ignored).
Source: none: infrastructure
Kind: L -/
theorem clsLe_iabm : IABM clsLe := by
  intro a a' r
  have : mUnp (dirac (a, r)) = mUnp (dirac (a', r)) := by simp [mUnp, mass]
  exact ⟨by unfold clsLe; rw [this], by unfold clsLe; rw [this]⟩

/-- The counter-model satisfies IBIL (substitution form).
Source: none: infrastructure
Kind: L -/
theorem clsLe_ibilSub : IBILsub clsLe := by
  intro X Y Z p hp h
  have hXY : (0 < mUnp X ↔ 0 < mUnp Y) :=
    ⟨(posInd_le_iff _ _).mp h.2, (posInd_le_iff _ _).mp h.1⟩
  have key : (0 < mUnp (mix p hp X Z) ↔ 0 < mUnp (mix p hp Y Z)) := by
    rw [mUnp_mix, mUnp_mix, pos_mix_iff (mUnp_nonneg X) (mUnp_nonneg Z) hp,
      pos_mix_iff (mUnp_nonneg Y) (mUnp_nonneg Z) hp, hXY]
  exact ⟨(posInd_le_iff _ _).mpr key.mpr, (posInd_le_iff _ _).mpr key.mp⟩

/-- The counter-model satisfies Thorstad's Monotonicity.
Source: Thorstad 2026 §4.1 l. 142
Kind: L -/
theorem clsLe_monotonicity : Monotonicity clsLe := by
  intro X Y p q hp hq hpq hXY
  unfold clsLe at *
  rw [posInd_le_iff] at hXY ⊢
  rw [mUnp_mix, mUnp_mix, pos_mix_iff (mUnp_nonneg X) (mUnp_nonneg Y) hq,
    pos_mix_iff (mUnp_nonneg X) (mUnp_nonneg Y) hp]
  have hp0 : 0 < p := lt_of_le_of_lt hq.1 hpq
  rintro (⟨_, hX⟩ | ⟨_, hY⟩)
  · exact Or.inl ⟨hp0, hX⟩
  · exact Or.inl ⟨hp0, hXY hY⟩

section thorstad

variable (f g h : ℝ) (hf : 0 ≤ f) (hfg : f < g) (hgh : g < h) (hh : h ≤ 1)

/-- In the counter-model, `U a ≻ P a` for every `a`.
Source: [[lit-shutdown-prefs-mandate]] Target 4
Kind: L -/
theorem clsLe_lt_UP (a : Act) :
    lt clsLe ((witness f g h hf hfg hgh hh).U a) ((witness f g h hf hfg hgh hh).P a) := by
  rw [witness_P, witness_U]
  unfold lt clsLe
  rw [posInd_le_iff, posInd_le_iff]
  simp [mUnp, mass]

/-- In the counter-model, Prevent and Leave are indifferent (both have positive unpressed mass),
so the state is **not** shutdown-averse.
Source: [[lit-shutdown-prefs-mandate]] Target 4
Kind: L -/
theorem clsLe_not_averse : ¬ (witness f g h hf hfg hgh hh).ShutdownAverse clsLe := by
  rintro ⟨⟨_, hne⟩, _⟩
  apply hne
  unfold clsLe
  rw [posInd_le_iff]
  intro _
  rw [act, mUnp_mix]
  simp only [witness_P, witness_U]
  simp [mUnp, mass, witness, prob]
  linarith

/-- **Thorstad's Monotonicity restatement of Theorem 1 is false.** Thorstad §4.1 l. 146: "Theorem
1: In Shutdown-Influencing States where the agent prefers (disprefers) some predicted unpressed
lottery U to some predicted pressed lottery P, the agent will be shutdown-averse
(shutdown-seeking)", with Better Chances replaced (l. 142) by Monotonicity `X ≽ Y → p > q →
pX+(1−p)Y ≽ qX+(1−q)Y`. Reading: the First Theorem's clause 1 with `Monotonicity` in place of
`BetterChances`, all other conditions kept (Completeness added for good measure). Refuted by the
counter-model `clsLe` on the witness state with `(f, g, h) = (1/4, 1/2, 3/4)`. Surviving
neighbour: `first_theorem_averse` under `StrictMonotone`, which Better Chances implies and
Monotonicity does not. Severity: local error in Thorstad (his §4.2 objection does not use it).
Robustness (audit round 1, fidelity non-blocking 3, adversarial N8): (i) `clsLe` puts every
lottery in one of two classes (positive / zero unpressed mass), both closed under mixture, so it
satisfies not only `IBILsub` but any reading of the sublottery schema — the refutation does not
depend on the ATTRIBUTION-UNVETTED reading of IBIL; (ii) Thorstad's sentence reads "some
predicted unpressed lottery U to *some* predicted pressed lottery P" (not "the corresponding");
the refuted universal uses corresponding pairs, and the counter-model has `U a ≻ P b` for all
`a, b` (its `lt` depends only on the rest-trajectory), so both readings are refuted; (iii)
Completeness is an added antecedent, which makes the refuted statement weaker and the refutation
stronger.
Source: Thorstad 2026 §4.1 ll. 140–148; corr-refs-058; [[lit-shutdown-prefs-mandate]] Target 4
Kind: N−
Fidelity: exact (of the restated theorem)
Hyps: (a) all -/
theorem thorstad_monotonicity_restatement_refuted :
    ¬ ∀ (S : SIS (Fin 2)) (le : Lottery (Act × Fin 2) → Lottery (Act × Fin 2) → Prop),
      Weak.Transitive le → Complete le → IABM le → IBILsub le → Monotonicity le →
      (∃ a, lt le (S.U a) (S.P a)) → S.ShutdownAverse le := by
  intro hall
  have hS := hall (witness (1/4) (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)) clsLe clsLe_transitive clsLe_complete clsLe_iabm clsLe_ibilSub
    clsLe_monotonicity ⟨.Leave, clsLe_lt_UP _ _ _ _ _ _ _ .Leave⟩
  exact clsLe_not_averse _ _ _ _ _ _ _ hS

/-- The refutation is not rescued by `f = 0`: the same counter-model works on the state
`(f, g, h) = (0, 1/2, 1)` (mandate-writer claim verified).
Source: [[lit-shutdown-prefs-mandate]] Target 4 ("Check whether `f = 0` rescues it")
Kind: N−
Fidelity: n/a -/
theorem thorstad_refuted_f_zero :
    ¬ ∀ (le : Lottery (Act × Fin 2) → Lottery (Act × Fin 2) → Prop),
      Weak.Transitive le → Complete le → IABM le → IBILsub le → Monotonicity le →
      (∃ a, lt le ((witness 0 (1/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).U a)
        ((witness 0 (1/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).P a)) →
      (witness 0 (1/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).ShutdownAverse le := by
  intro hall
  have hS := hall clsLe clsLe_transitive clsLe_complete clsLe_iabm clsLe_ibilSub
    clsLe_monotonicity ⟨.Leave, clsLe_lt_UP _ _ _ _ _ _ _ .Leave⟩
  exact clsLe_not_averse _ _ _ _ _ _ _ hS

end thorstad

end SIS

end Cleanroom.Lit.LitShutdownPrefs
