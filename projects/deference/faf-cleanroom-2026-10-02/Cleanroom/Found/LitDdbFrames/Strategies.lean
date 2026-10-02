import Cleanroom.Found.LitDdbFrames.Basic

/-!
# Strategies: argmax choices, the two-option witness, Value → Weak Value

Package `lit-ddb-frames`, Target 3. The recommended strategy that exists for every nonempty menu
is built *per candidate* (a function of the expert's distribution), so the cell constraint holds by
construction; the informed tie-breaking version (among `E_ρ`-maximisers pick an
`E_{P̂_ρ}`-maximiser) is the strategy Lemma 7.3 needs. The two-option witness identity is
exported in the exact product-form expression `def-lattice` states over FAF LUVs.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Maximisers and the informed choice -/

/-- The options of `𝒪` with maximal expected utility under `ρ`.
Source: [[Deference Done Better]] App. B Lemma 7.3 l. 544 (`M_j`)
Kind: D
Fidelity: exact -/
def maximizers (𝒪 : DecisionProblem W) (ρ : W → ℝ) : Finset (W → ℝ) :=
  𝒪.filter (fun o => ∀ o' ∈ 𝒪, E ρ o' ≤ E ρ o)

/-- Membership in the maximisers.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_maximizers {𝒪 : DecisionProblem W} {ρ o : W → ℝ} :
    o ∈ maximizers 𝒪 ρ ↔ o ∈ 𝒪 ∧ ∀ o' ∈ 𝒪, E ρ o' ≤ E ρ o := by
  simp [maximizers]

/-- A nonempty menu has a maximiser under every `ρ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem maximizers_nonempty {𝒪 : DecisionProblem W} (h : 𝒪.Nonempty) (ρ : W → ℝ) :
    (maximizers 𝒪 ρ).Nonempty := by
  obtain ⟨o, ho, hmax⟩ := 𝒪.exists_max_image (E ρ) h
  exact ⟨o, mem_maximizers.2 ⟨ho, hmax⟩⟩

/-- The *informed choice* at a candidate `ρ`: among the `E_ρ`-maximisers of `𝒪`, one that
maximises the informed expectation `E_{P̂_ρ}` (DDB's tie-breaking in Lemma 7.3).
Source: [[Deference Done Better]] App. B Lemma 7.3 l. 544
Kind: D
Fidelity: exact -/
def Frame.informedChoice (F : Frame W) (𝒪 : DecisionProblem W) (h : 𝒪.Nonempty) (ρ : W → ℝ) :
    W → ℝ :=
  Classical.choose
    ((maximizers 𝒪 ρ).exists_max_image (E (F.informed ρ)) (maximizers_nonempty h ρ))

/-- The informed choice is an `E_ρ`-maximiser and maximises `E_{P̂_ρ}` among them.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.informedChoice_spec (F : Frame W) (𝒪 : DecisionProblem W) (h : 𝒪.Nonempty)
    (ρ : W → ℝ) :
    F.informedChoice 𝒪 h ρ ∈ maximizers 𝒪 ρ ∧
      ∀ o ∈ maximizers 𝒪 ρ, E (F.informed ρ) o ≤ E (F.informed ρ) (F.informedChoice 𝒪 h ρ) :=
  Classical.choose_spec
    ((maximizers 𝒪 ρ).exists_max_image (E (F.informed ρ)) (maximizers_nonempty h ρ))

/-- The *informed strategy*: the informed choice at each world's candidate. Cellwise by
construction.
Source: [[Deference Done Better]] App. B Lemma 7.3 l. 544
Kind: D
Fidelity: exact -/
def Frame.informedStrategy (F : Frame W) (𝒪 : DecisionProblem W) (h : 𝒪.Nonempty) :
    W → (W → ℝ) :=
  fun w => F.informedChoice 𝒪 h (F.P w)

/-- The informed strategy is recommended.
Source: none: infrastructure (Target 3)
Kind: L
Fidelity: n/a -/
theorem Frame.informedStrategy_recommended (F : Frame W) (𝒪 : DecisionProblem W)
    (h : 𝒪.Nonempty) : F.Recommended 𝒪 (F.informedStrategy 𝒪 h) := by
  refine ⟨⟨fun w => (mem_maximizers.1 (F.informedChoice_spec 𝒪 h (F.P w)).1).1,
    fun w v e => by simp only [Frame.informedStrategy, e]⟩, ?_⟩
  intro w o ho
  exact (mem_maximizers.1 (F.informedChoice_spec 𝒪 h (F.P w)).1).2 o ho

/-- The informed strategy maximises the informed expectation among the maximisers at each
world.
Source: none: infrastructure (Target 3)
Kind: L
Fidelity: n/a -/
theorem Frame.informedStrategy_informed_le (F : Frame W) (𝒪 : DecisionProblem W)
    (h : 𝒪.Nonempty) (w : W) {o : W → ℝ} (ho : o ∈ maximizers 𝒪 (F.P w)) :
    E (F.informed (F.P w)) o ≤ E (F.informed (F.P w)) (F.informedStrategy 𝒪 h w) :=
  (F.informedChoice_spec 𝒪 h (F.P w)).2 o ho

/-- **Target 3.** Value implies Weak Value: a recommended strategy exists for every nonempty
menu (the informed strategy).
Source: [[Deference Done Better]] App. B §7.2 l. 571 ("full Value (obviously) entails Weak
Value (since there always is at least one recommended strategy)")
Kind: L
Fidelity: exact -/
theorem Value.weakValue {π : W → ℝ} {F : Frame W} (h : Value π F) : WeakValue π F :=
  fun 𝒪 hne => ⟨F.informedStrategy 𝒪 hne, F.informedStrategy_recommended 𝒪 hne,
    h 𝒪 hne _ (F.informedStrategy_recommended 𝒪 hne)⟩

/-! ## The two-option witness -/

/-- The two-option witness strategy is recommended for the menu `{X, const s}`.
Source: [[Deference Done Better]] App. B Lemma 7.1 l. 486
Kind: L
Fidelity: n/a -/
theorem Frame.twoOption_recommended (F : Frame W) (X : W → ℝ) (s : ℝ) :
    F.Recommended {X, fun _ => s} (F.twoOption X s) := by
  refine ⟨⟨fun w => ?_, fun w v e => ?_⟩, fun w o ho => ?_⟩
  · unfold Frame.twoOption
    split_ifs <;> simp
  · simp only [Frame.twoOption, e]
  · have hE := E_const (F.P_mem w) s
    simp only [mem_insert, mem_singleton] at ho
    unfold Frame.twoOption
    split_ifs with hs
    · rcases ho with rfl | rfl
      · exact le_rfl
      · rw [hE]; exact hs
    · rcases ho with rfl | rfl
      · rw [hE]; exact (not_le.1 hs).le
      · exact le_rfl

/-- **Target 3, the two-option witness identity.** For the menu `{X, const s}` and the witness
strategy `S_wit w := if s ≤ E_{P_w}(X) then X else const s`,
`E_π(S_wit) − s = ∑ w, π w · (X w − s) · 𝟙[s ≤ E_{P_w}(X)]` — literally the product form of
Total Trust. (Bridge to `def-lattice`'s two-option identity over FAF LUVs.)
Source: [[Deference Done Better]] §2 l. 190, App. B Lemma 7.1 l. 489; mandate Target 3
Kind: L
Fidelity: exact -/
theorem stratValue_twoOption {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) (X : W → ℝ)
    (s : ℝ) :
    stratValue π (F.twoOption X s) - s =
      ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
  have hs : ∑ w, π w * s = s := by rw [← sum_mul, hπ.2, one_mul]
  have e : stratValue π (F.twoOption X s) - s =
      ∑ w, (π w * (F.twoOption X s) w w - π w * s) := by
    rw [sum_sub_distrib, hs]; rfl
  rw [e]
  apply sum_congr rfl
  intro w _
  unfold Frame.twoOption
  split_ifs <;> simp <;> ring

/-- **Target 3.** Total Trust is exactly "the two-option witness strategy is worth at least the
constant" for every `X, s`.
Source: [[Deference Done Better]] §2 l. 190; mandate Target 3
Kind: L
Fidelity: exact -/
theorem totalTrust_iff_twoOption {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} :
    TotalTrust π F ↔ ∀ (X : W → ℝ) (s : ℝ), s ≤ stratValue π (F.twoOption X s) := by
  constructor
  · intro h X s
    have := h X s
    rw [← stratValue_twoOption hπ] at this
    linarith
  · intro h X s
    rw [← stratValue_twoOption hπ]
    linarith [h X s]

/-- **Value on two-option menus**: Value restricted to menus `{X, const s}`, over *all*
recommended strategies (ties at `E_w(X) = s` broken cellwise either way). Not "Value ⟺ Total
Trust": its equivalence with Total Trust is a corollary of Theorem 7.6 (`Cycle.lean`).
Source: [[Deference Done Better]] §2 l. 190 (the ⇐ sketch's menus); mandate Target 3
Kind: D
Fidelity: variant: Value restricted to two-option menus -/
def ValueTwoOption (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (X : W → ℝ) (s : ℝ), ∀ S, F.Recommended {X, fun _ => s} S →
    ∀ o ∈ ({X, fun _ => s} : DecisionProblem W), E π o ≤ stratValue π S

/-- Value implies Value on two-option menus.
Source: none: infrastructure (Target 3)
Kind: L
Fidelity: n/a -/
theorem Value.twoOption {π : W → ℝ} {F : Frame W} (h : Value π F) : ValueTwoOption π F :=
  fun X _s S hS o ho => h _ (insert_nonempty _ _) S hS o ho

/-- Value on two-option menus implies Total Trust (through the witness strategy).
Source: [[Deference Done Better]] §2 l. 190; mandate Target 3
Kind: L
Fidelity: exact -/
theorem ValueTwoOption.totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ValueTwoOption π F) : TotalTrust π F := by
  rw [totalTrust_iff_twoOption hπ]
  intro X s
  have := h X s _ (F.twoOption_recommended X s) (fun _ => s) (by simp)
  rwa [E_const hπ] at this

end

end Cleanroom.Found.LitDdbFrames
