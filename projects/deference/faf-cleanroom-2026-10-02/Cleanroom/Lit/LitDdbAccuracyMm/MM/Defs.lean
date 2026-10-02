import Cleanroom.Found.LitDdbFrames

/-!
# Managing Misalignment — definitions of record (Target 13)

Herrmann et al. 2025 (MM) lift DDB's frames to a principal–agent setting. MM's *probability
frame* `⟨Ω, F, π, P⟩` is the foundation's `Frame W` with the deferrer `π` (`abbrev`, not a new
structure). A *generalized frame* adds consequences `C`, the principal's utility `u`, the agent's
type `(P_ω, V_ω)` at each world, and the admissible acts `A`; a *behaviour* `B_ω` chooses on each
menu an act maximising the agent's expected utility at `ω` (MM Definition 3.3: "there exists some
utility function `V_ω` and probability distribution `P_ω` such that for any decision problem `A`:
`B_ω(A) ∈ argmax E_{P_ω}(V_ω ∘ a)`"). Note that MM's definition lets `B_ω` depend on `ω` *within*
a type cell — the encoding artefact behind Target 15's refutations; `TypeMeasurable` is the
repaired reading.

Conditioning is in product form throughout: the conditional preference `E_π(u(a) | [ω]) >
E_π(u(b) | [ω])` is `∑_{[ω]} π u(b) < ∑_{[ω]} π u(a)` (the common factor `π([ω])` cancels; a
`π`-null type imposes nothing).

§3.4's scoring framework is indexed: gambles `gam : ι → W → ℝ` with weights `μ : ι → ℝ` (a
finitely supported measure on gamble-space is an indexed family), and the decision rule
`D : W → Finset ι` is *state-indexed* — MM's `D` is the constant case, but their §4.1–4.2 agents
decide from information that is part of the state, so the appendices' tables are state-indexed
rules. The gain is parametrised by convention (`gainPrinted`: accepted winners only, §3.4's
displayed formula and §4.3's tables; `gainCorrect`: rejected losers count too, §4.1–4.2 and
Appendices A–B).
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {C : Type} [DecidableEq C]

/-! ## Probability frames and generalized frames -/

/-- MM's probability frame `⟨Ω, F, π, P⟩` *is* DDB's finite frame (the deferrer `π` travels
separately, as in the foundation).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Def. 3.1 l. 75
Kind: D
Fidelity: exact -/
abbrev ProbFrame (W : Type) [Fintype W] := Frame W

/-- Acts `a : Ω → C` (Savage).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 91
Kind: D
Fidelity: exact -/
abbrev Act (W C : Type) := W → C

/-- A **generalized frame** `⟨Ω, F, π, u, B, A, C⟩` minus `π` and `B`: the principal's utility
`u`, the agent's type at each world (`Pag ω` a distribution, `V ω` a utility), and the set `A` of
admissible acts (decision problems are its nonempty subsets).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Def. 3.3 l. 93
Kind: D
Fidelity: exact (the behaviour `B` is a separate object, `IsBehaviour`, so that Theorem 3.4 can
quantify over it) -/
structure GFrame (W C : Type) [Fintype W] where
  /-- the principal's utility -/
  u : C → ℝ
  /-- the agent's beliefs at each world -/
  Pag : W → W → ℝ
  /-- each row is a distribution -/
  Pag_mem : ∀ w, Pag w ∈ stdSimplex ℝ W
  /-- the agent's utility at each world -/
  V : W → C → ℝ
  /-- the admissible acts -/
  A : Finset (W → C)

/-- The agent's expected utility of an act at `ω`: `E_{P_ω}(V_ω ∘ a)`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Def. 3.3 l. 93
Kind: D
Fidelity: exact -/
def GFrame.agentEU (G : GFrame W C) (ω : W) (a : W → C) : ℝ := E (G.Pag ω) (G.V ω ∘ a)

/-- A **behaviour**: on every nonempty decision problem `𝒜 ⊆ A` and at every world, `B ω 𝒜` is
an act of `𝒜` maximising the agent's expected utility at `ω` (MM Definition 3.3's `B_ω`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Def. 3.3 l. 93
Kind: D
Fidelity: exact -/
def IsBehaviour (G : GFrame W C) (B : W → Finset (W → C) → (W → C)) : Prop :=
  ∀ ω (𝒜 : Finset (W → C)), 𝒜 ⊆ G.A → 𝒜.Nonempty →
    B ω 𝒜 ∈ 𝒜 ∧ ∀ a ∈ 𝒜, G.agentEU ω a ≤ G.agentEU ω (B ω 𝒜)

/-- The **type cell** `[ω] := {ω' : (P_ω', V_ω') = (P_ω, V_ω)}`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 95
Kind: D
Fidelity: exact -/
def tcell (G : GFrame W C) (ω : W) : Finset W := by
  classical exact
  univ.filter (fun ω' => G.Pag ω' = G.Pag ω ∧ G.V ω' = G.V ω)

/-- **Clarity**: the agent is certain of its own type — `P_ω(ω') = 0` for `ω' ∉ [ω]`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 95
Kind: D
Fidelity: exact -/
def Clarity (G : GFrame W C) : Prop := ∀ ω ω', ω' ∉ tcell G ω → G.Pag ω ω' = 0

/-- The spliced act `a` on `X`, `a'` off `X` (MM's `a^X_{a'}`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 415
Kind: D
Fidelity: exact -/
def splice (X : Finset W) (a a' : W → C) : W → C := fun ω => if ω ∈ X then a ω else a' ω

/-- **Richness**: `A` is closed under splicing.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 415
Kind: D
Fidelity: exact -/
def Richness (G : GFrame W C) : Prop :=
  ∀ a ∈ G.A, ∀ a' ∈ G.A, ∀ X : Finset W, splice X a a' ∈ G.A

/-- **Constant acts**: two constant acts in `A` whose consequences the principal strictly ranks.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 419
Kind: D
Fidelity: exact -/
def ConstantActs (G : GFrame W C) : Prop :=
  ∃ c₁ c₂ : C, G.u c₂ < G.u c₁ ∧ (fun _ => c₁) ∈ G.A ∧ (fun _ => c₂) ∈ G.A

/-- **Stochastic choice, as printed (with the principal's `u`)**: if `a, b` in a decision problem
tie under `E_ω(u(·))` and `B_ω` picks `a`, some `π`-positive world of the same type picks `b`.
Printed with `u` (l. 417); the intended reading is surely `V_ω` (ATTRIBUTION-UNVETTED), so both
are defined. Read literally, `a = b` is allowed.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 417
Kind: D
Fidelity: exact (as printed) -/
def StochasticChoiceU (G : GFrame W C) (π : W → ℝ) (B : W → Finset (W → C) → (W → C)) : Prop :=
  ∀ (𝒜 : Finset (W → C)), 𝒜 ⊆ G.A → ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ ω,
    E (G.Pag ω) (G.u ∘ a) = E (G.Pag ω) (G.u ∘ b) → B ω 𝒜 = a →
      ∃ ω', 0 < π ω' ∧ ω' ∈ tcell G ω ∧ B ω' 𝒜 = b

/-- **Stochastic choice with the agent's `V_ω`** (the presumably intended reading).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 417
Kind: D
Fidelity: variant: `V_ω` in place of the printed `u` -/
def StochasticChoiceV (G : GFrame W C) (π : W → ℝ) (B : W → Finset (W → C) → (W → C)) : Prop :=
  ∀ (𝒜 : Finset (W → C)), 𝒜 ⊆ G.A → ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ ω,
    G.agentEU ω a = G.agentEU ω b → B ω 𝒜 = a →
      ∃ ω', 0 < π ω' ∧ ω' ∈ tcell G ω ∧ B ω' 𝒜 = b

/-- The value of delegating a menu to a behaviour: `E_π(u(B(𝒜))) = ∑ ω, π ω · u(B_ω(𝒜)(ω))`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 95
Kind: D
Fidelity: exact -/
def delegValue (π : W → ℝ) (G : GFrame W C) (B : W → Finset (W → C) → (W → C))
    (𝒜 : Finset (W → C)) : ℝ := ∑ ω, π ω * G.u (B ω 𝒜 ω)

/-- **The principal values the agent (fixed behaviour)**: for every nonempty decision problem
`𝒜 ⊆ A` and act `a ∈ 𝒜`, `E_π(u(a)) ≤ E_π(u(B(𝒜)))`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.2 l. 95
Kind: D
Fidelity: exact -/
def ValuesB (π : W → ℝ) (G : GFrame W C) (B : W → Finset (W → C) → (W → C)) : Prop :=
  ∀ 𝒜 ⊆ G.A, 𝒜.Nonempty → ∀ a ∈ 𝒜, E π (G.u ∘ a) ≤ delegValue π G B 𝒜

/-- **Type-measurable** behaviour: `B_ω` depends on `ω` only through the agent's type.
Source: none: the repaired reading of MM Definition 3.3 (mandate Target 13); DDB's cell
constraint on strategies (foundation `Frame.IsStrategy`)
Kind: D
Fidelity: variant: strengthens MM's `B` by the cell constraint -/
def TypeMeasurable (G : GFrame W C) (B : W → Finset (W → C) → (W → C)) : Prop :=
  ∀ ω ω' 𝒜, ω' ∈ tcell G ω → B ω 𝒜 = B ω' 𝒜

/-- The conditional expected utility of `a` on the type cell of `ω`, in product form:
`∑_{w ∈ [ω]} π w · u(a w)` (`= E_π(u(a) | [ω]) · π([ω])`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97
Kind: D
Fidelity: exact (product form) -/
def cellEU (π : W → ℝ) (G : GFrame W C) (ω : W) (a : W → C) : ℝ :=
  ∑ w ∈ tcell G ω, π w * G.u (a w)

/-- **Strict conditional preference agreement** (Theorem 3.4's right-hand side): for all
`a, b ∈ A` and every `ω` whose type has positive `π`-mass, if
`E_π(u(a) | [ω]) > E_π(u(b) | [ω])` then `E_ω(V_ω(a)) > E_ω(V_ω(b))`. A `π`-null type imposes
nothing (the guard is redundant: the product inequality is then `0 < 0`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] Thm 3.4 l. 97,
App. D l. 421
Kind: D
Fidelity: exact (product form) -/
def StrictAgree (π : W → ℝ) (G : GFrame W C) : Prop :=
  ∀ a ∈ G.A, ∀ b ∈ G.A, ∀ ω, 0 < mass π (tcell G ω) →
    cellEU π G ω b < cellEU π G ω a → G.agentEU ω b < G.agentEU ω a

/-- **Weak conditional preference agreement**: the same with `≤` in the conclusion (what MM's
proof establishes before invoking stochastic choice).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. D l. 429
Kind: D
Fidelity: exact (product form) -/
def WeakAgree (π : W → ℝ) (G : GFrame W C) : Prop :=
  ∀ a ∈ G.A, ∀ b ∈ G.A, ∀ ω, 0 < mass π (tcell G ω) →
    cellEU π G ω b < cellEU π G ω a → G.agentEU ω b ≤ G.agentEU ω a

/-! ## §3.4: decision-based scoring -/

section Scoring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The **ideal set** at `ω`: the gambles with nonnegative payoff there.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 113
Kind: D
Fidelity: exact (indexed gambles) -/
def ideal (gam : ι → W → ℝ) (ω : W) : Finset ι := univ.filter (fun i => 0 ≤ gam i ω)

/-- The **expected loss** of a (state-indexed) decision rule:
`∑ ω, π ω ∑_{i ∈ D ω ∆ I_ω} μ i |g_i(ω)|`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 115
Kind: D
Fidelity: variant: gambles indexed by `ι` with weights `μ`; `D` state-indexed (MM's `D` is the
constant case; §4.1–4.2's `D_B` are state-indexed) -/
def loss (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) : ℝ :=
  ∑ ω, π ω * ∑ i, μ i * |gam i ω| *
    (if (i ∈ D ω ∧ gam i ω < 0) ∨ (i ∉ D ω ∧ 0 ≤ gam i ω) then 1 else 0)

/-- The **gain, printed convention**: accepted winners only,
`∑ ω, π ω ∑_{i ∈ D ω ∩ I_ω} μ i |g_i(ω)|` (§3.4's displayed formula; what §4.3 uses).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 121
Kind: D
Fidelity: exact (as printed) -/
def gainPrinted (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) : ℝ :=
  ∑ ω, π ω * ∑ i, μ i * |gam i ω| * (if i ∈ D ω ∧ 0 ≤ gam i ω then 1 else 0)

/-- The **gain, correct-decisions convention**: accepted winners and rejected losers
(what §4.1–4.2 and Appendices A–B use: "a gain if Bob opens on a positive value or correctly
avoids opening on a negative value").
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. A l. 199,
App. B l. 355
Kind: D
Fidelity: variant: the appendices' convention -/
def gainCorrect (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) : ℝ :=
  ∑ ω, π ω * ∑ i, μ i * |gam i ω| *
    (if (i ∈ D ω ∧ 0 ≤ gam i ω) ∨ (i ∉ D ω ∧ gam i ω < 0) then 1 else 0)

/-- The net score `S = L − G`, printed convention.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 123
Kind: D
Fidelity: exact -/
def scorePrinted (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) : ℝ :=
  loss π gam μ D - gainPrinted π gam μ D

/-- The net score `S = L − G`, correct-decisions convention.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 123
Kind: D
Fidelity: variant: the appendices' convention -/
def scoreCorrect (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) : ℝ :=
  loss π gam μ D - gainCorrect π gam μ D

/-- **`L + G` is independent of the rule** under the correct-decisions convention: every
gamble at every state is exactly one of an error or a correct decision, so
`L(D) + G(D) = ∑ ω, π ω ∑ i, μ i |g_i(ω)|`. Hence `S(D_A) ≤ S(D_π) ⟺ L(D_A) ≤ L(D_π)` exactly
under this convention (`scoreCorrect_le_iff`), and not under the printed one (`MM/Examples`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 117–123;
item 087
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem loss_add_gainCorrect (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D : W → Finset ι) :
    loss π gam μ D + gainCorrect π gam μ D = ∑ ω, π ω * ∑ i, μ i * |gam i ω| := by
  unfold loss gainCorrect
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro ω _
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hD : i ∈ D ω <;> by_cases hg : 0 ≤ gam i ω <;> simp [hD, hg, not_lt.2]

/-- Under the correct-decisions convention, comparing scores is comparing losses.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 119, l. 123
Kind: L
Fidelity: exact -/
theorem scoreCorrect_le_iff (π : W → ℝ) (gam : ι → W → ℝ) (μ : ι → ℝ) (D D' : W → Finset ι) :
    scoreCorrect π gam μ D ≤ scoreCorrect π gam μ D' ↔ loss π gam μ D ≤ loss π gam μ D' := by
  have h1 := loss_add_gainCorrect π gam μ D
  have h2 := loss_add_gainCorrect π gam μ D'
  unfold scoreCorrect
  constructor <;> intro h <;> linarith

end Scoring

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM
