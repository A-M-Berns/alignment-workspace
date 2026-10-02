import Cleanroom.Lit.LitDdbFacts.Cells

/-!
# Fixed-option Dutch books (§1 l. 135, fns 20–22, glossary l. 428)

Package `lit-ddb-facts`, Target 9. DDB give two inequivalent definitions of a fixed-option Dutch
book: fn 20 demands a *sure* strict loss at every world; the glossary demands an *almost-sure*
loss (`π(O + S ≤ 0) = 1` and `π(O + S < 0) > 0`); fn 22 refutes even an *expected* loss. The
book is parametrised by the loss grade, and the theorem of record is that failure of Value is
equivalent to the existence of a book at each of the three grades: (⇒) fn 21's construction
produces a sure loss `−ε`; (⇐) fn 22 needs only an expected loss.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The three loss grades -/

/-- Sure loss: the combined payoff is strictly negative at every world (fn 20).
Source: [[Deference Done Better]] fn 20
Kind: D
Fidelity: exact -/
def SureLoss (Z : W → ℝ) : Prop := ∀ w, Z w < 0

/-- Almost-sure loss (glossary): `π(Z ≤ 0) = 1` in product form (`∑ w, π w · max 0 (Z w) = 0`)
and `π(Z < 0) > 0`.
Source: [[Deference Done Better]] glossary l. 428
Kind: D
Fidelity: exact -/
def AlmostSureLoss (π : W → ℝ) (Z : W → ℝ) : Prop :=
  ∑ w, π w * max 0 (Z w) = 0 ∧ 0 < mass π (univ.filter (fun w => Z w < 0))

/-- Expected loss: `E_π(Z) < 0` (fn 22's weakest grade).
Source: [[Deference Done Better]] fn 22
Kind: D
Fidelity: exact -/
def ExpectedLoss (π : W → ℝ) (Z : W → ℝ) : Prop := E π Z < 0

/-- A **fixed-option Dutch book** against the transition `π → P`, at a loss grade `loss`: two
decision problems `𝒪₁` (before) and `𝒪₂` (after) both containing the "no bet" option `0`; an
option `O ∈ 𝒪₁` maximising `π`-expectation in `𝒪₁`; a strategy `S` recommended by the frame for
`𝒪₂`; and the combined payoff `w ↦ O w + S_w(w)` suffers the loss.
Source: [[Deference Done Better]] §1 l. 135, fn 20, glossary l. 428
Kind: D
Fidelity: exact (the loss grade is a parameter) -/
def FixedOptionBook (π : W → ℝ) (F : Frame W) (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ)
    (S : W → (W → ℝ)) (loss : (W → ℝ) → Prop) : Prop :=
  (fun _ => (0 : ℝ)) ∈ 𝒪₁ ∧ (fun _ => (0 : ℝ)) ∈ 𝒪₂ ∧ O ∈ 𝒪₁ ∧ (∀ o ∈ 𝒪₁, E π o ≤ E π O) ∧
    F.Recommended 𝒪₂ S ∧ loss (fun w => O w + S w w)

/-- A sure loss is an almost-sure loss.
Source: [[Deference Done Better]] fn 20 vs glossary l. 428
Kind: L
Fidelity: n/a -/
theorem AlmostSureLoss.of_sureLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {Z : W → ℝ}
    (h : SureLoss Z) : AlmostSureLoss π Z := by
  refine ⟨sum_eq_zero fun w _ => ?_, ?_⟩
  · rw [max_eq_left (h w).le, mul_zero]
  · have : univ.filter (fun w => Z w < 0) = univ := by
      ext w; simp [h w]
    rw [this, mass_univ hπ]
    exact one_pos

/-- An almost-sure loss is an expected loss.
Source: [[Deference Done Better]] glossary l. 428 vs fn 22
Kind: L
Fidelity: n/a -/
theorem ExpectedLoss.of_almostSureLoss {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {Z : W → ℝ}
    (h : AlmostSureLoss π Z) : ExpectedLoss π Z := by
  obtain ⟨h0, hpos⟩ := h
  obtain ⟨w₀, hw₀, hπw₀⟩ := (mass_pos_iff hπ).1 hpos
  rw [mem_filter] at hw₀
  unfold ExpectedLoss E
  rw [← h0]
  apply sum_lt_sum
  · intro w _
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hπ w)
  · refine ⟨w₀, mem_univ _, ?_⟩
    rw [max_eq_left hw₀.2.le, mul_zero]
    exact mul_neg_of_pos_of_neg hπw₀ hw₀.2

/-- A sure loss is an expected loss.
Source: [[Deference Done Better]] fn 20 vs fn 22
Kind: L
Fidelity: n/a -/
theorem ExpectedLoss.of_sureLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {Z : W → ℝ}
    (h : SureLoss Z) : ExpectedLoss π Z :=
  ExpectedLoss.of_almostSureLoss hπ.1 (AlmostSureLoss.of_sureLoss hπ h)

/-- The expectation of the combined payoff splits: `E_π(O + S) = E_π(O) + E_π(S)`.
Source: [[Deference Done Better]] fn 22
Kind: L
Fidelity: n/a -/
theorem E_combined (π : W → ℝ) (O : W → ℝ) (S : W → (W → ℝ)) :
    E π (fun w => O w + S w w) = E π O + stratValue π S := by
  unfold E stratValue
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  ring

/-! ## Target 9: failure of Value ⟺ a Dutch book exists -/

/-- **Fn 21.** If `π` fails to value the frame, there is a fixed-option Dutch book with a sure
loss: from `E_π(S) < E_π(o)` on `𝒪` take `ε := (E_π(o) − E_π(S))/2`, `𝒪₁ = {0, o − S − ε}`
(`o − S − ε` is `π`-optimal), `𝒪₂ = {o' − o : o' ∈ 𝒪}` (`0 = o − o` is in it), `S'_w := S_w − o`
(recommended: cell constraint and optimality are inherited); the combined payoff is `−ε` at
every world.
Source: [[Deference Done Better]] fn 21
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`; `¬ Value` is the antecedent -/
theorem exists_book_sureLoss_of_not_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ¬ Value π F) :
    ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
      FixedOptionBook π F 𝒪₁ 𝒪₂ O S SureLoss := by
  unfold Value at h
  push Not at h
  obtain ⟨𝒪, _, S, hS, o, ho, hlt⟩ := h
  set ε : ℝ := (E π o - stratValue π S) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set O : W → ℝ := fun w => o w - S w w - ε with hO
  have hEO : E π O = E π o - stratValue π S - ε := by
    have : O = o - (fun w => S w w) - (fun _ => ε) := by funext w; simp [hO]
    rw [this, E_sub_right, E_sub_right, E_const hπ, stratValue_eq_E]
  refine ⟨{fun _ => 0, O}, 𝒪.image (fun o' => o' - o), O, fun w => S w - o, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp
  · rw [mem_image]
    exact ⟨o, ho, by funext w; simp⟩
  · simp
  · intro o' ho'
    simp only [mem_insert, mem_singleton] at ho'
    rcases ho' with rfl | rfl
    · rw [E_const hπ, hEO]
      linarith
    · exact le_rfl
  · refine ⟨⟨fun w => mem_image.2 ⟨S w, hS.mem w, rfl⟩, fun w v e => by
      show S w - o = S v - o
      rw [hS.cell e]⟩, ?_⟩
    intro w o' ho'
    rw [mem_image] at ho'
    obtain ⟨o'', ho'', rfl⟩ := ho'
    rw [E_sub_right, E_sub_right]
    have := hS.le w ho''
    linarith
  · intro w
    simp only [hO, Pi.sub_apply]
    linarith

/-- **Fn 22.** A fixed-option Dutch book with merely an *expected* loss already refutes Value:
`E_π(O) ≥ E_π(0) = 0` since `O` is `π`-optimal in `𝒪₁ ∋ 0`, and `E_π(S) ≥ E_π(0) = 0` by Value
on `𝒪₂ ∋ 0`; so `E_π(O + S) ≥ 0`.
Source: [[Deference Done Better]] fn 22
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem not_value_of_book_expectedLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    {𝒪₁ 𝒪₂ : DecisionProblem W} {O : W → ℝ} {S : W → (W → ℝ)}
    (hb : FixedOptionBook π F 𝒪₁ 𝒪₂ O S (ExpectedLoss π)) : ¬ Value π F := by
  intro hv
  obtain ⟨h01, h02, _, hmax, hS, hloss⟩ := hb
  have h1 : 0 ≤ E π O := by
    have := hmax _ h01
    rwa [E_const hπ] at this
  have h2 : 0 ≤ stratValue π S := by
    have := hv 𝒪₂ ⟨_, h02⟩ S hS _ h02
    rwa [E_const hπ] at this
  unfold ExpectedLoss at hloss
  rw [E_combined] at hloss
  linarith

/-- A book at a stronger loss grade is a book at a weaker one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem FixedOptionBook.mono {π : W → ℝ} {F : Frame W} {𝒪₁ 𝒪₂ : DecisionProblem W}
    {O : W → ℝ} {S : W → (W → ℝ)} {loss₁ loss₂ : (W → ℝ) → Prop}
    (hb : FixedOptionBook π F 𝒪₁ 𝒪₂ O S loss₁) (h : ∀ Z, loss₁ Z → loss₂ Z) :
    FixedOptionBook π F 𝒪₁ 𝒪₂ O S loss₂ :=
  ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, h _ hb.2.2.2.2.2⟩

/-- **Target 9, headline (fn 20's grade).** `π` fails to value the frame iff there is a
fixed-option Dutch book with a *sure* loss against the transition `π → P`.
Source: [[Deference Done Better]] §1 l. 135, fns 20–22; item 058
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem not_value_iff_exists_book_sureLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} : ¬ Value π F ↔ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
      FixedOptionBook π F 𝒪₁ 𝒪₂ O S SureLoss :=
  ⟨exists_book_sureLoss_of_not_value hπ, fun ⟨_, _, _, _, hb⟩ =>
    not_value_of_book_expectedLoss hπ (hb.mono fun _ hZ => ExpectedLoss.of_sureLoss hπ hZ)⟩

/-- **Target 9 (glossary's grade).** `π` fails to value the frame iff there is a fixed-option
Dutch book with an *almost-sure* loss.
Source: [[Deference Done Better]] glossary l. 428, fns 21–22
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem not_value_iff_exists_book_almostSureLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} : ¬ Value π F ↔ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
      FixedOptionBook π F 𝒪₁ 𝒪₂ O S (AlmostSureLoss π) :=
  ⟨fun h => by
    obtain ⟨𝒪₁, 𝒪₂, O, S, hb⟩ := exists_book_sureLoss_of_not_value hπ h
    exact ⟨𝒪₁, 𝒪₂, O, S, hb.mono fun _ hZ => AlmostSureLoss.of_sureLoss hπ hZ⟩,
   fun ⟨_, _, _, _, hb⟩ =>
    not_value_of_book_expectedLoss hπ (hb.mono fun _ hZ => ExpectedLoss.of_almostSureLoss hπ.1 hZ)⟩

/-- **Target 9 (fn 22's grade).** `π` fails to value the frame iff there is a fixed-option Dutch
book with an *expected* loss.
Source: [[Deference Done Better]] fn 22
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem not_value_iff_exists_book_expectedLoss {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    {F : Frame W} : ¬ Value π F ↔ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
      FixedOptionBook π F 𝒪₁ 𝒪₂ O S (ExpectedLoss π) :=
  ⟨fun h => by
    obtain ⟨𝒪₁, 𝒪₂, O, S, hb⟩ := exists_book_sureLoss_of_not_value hπ h
    exact ⟨𝒪₁, 𝒪₂, O, S, hb.mono fun _ hZ => ExpectedLoss.of_sureLoss hπ hZ⟩,
   fun ⟨_, _, _, _, hb⟩ => not_value_of_book_expectedLoss hπ hb⟩

/-- **Theorem 5.1, second bullet.** `π` values the frame iff no fixed-option Dutch book (sure
loss) exists against the transition `π → P`.
Source: [[Deference Done Better]] §5 l. 375 (Theorem 5.1), §1 l. 135
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem value_iff_no_book {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} :
    Value π F ↔ ¬ ∃ (𝒪₁ 𝒪₂ : DecisionProblem W) (O : W → ℝ) (S : W → (W → ℝ)),
      FixedOptionBook π F 𝒪₁ 𝒪₂ O S SureLoss := by
  rw [← not_value_iff_exists_book_sureLoss hπ, not_not]

end

end Cleanroom.Lit.LitDdbFacts
