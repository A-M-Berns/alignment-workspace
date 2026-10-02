import Cleanroom.Corrigibility.LegitNegStatic.Scorings
import Mathlib.Data.Prod.Lex

/-!
# The proposals P1–P5 under the diagonal readout R1, and the null convention

Package `legit-neg-static`, target 3. Sources: `clusters/B/fixtures/model.py:144-160`,
`clusters/C/fixtures/model.py:60-98`, pinned by [[corr-legit-neg-inventory]] item 002 and
[[corr-legit-neg-2-inventory]] item 2-003.

**The null convention of record is exclusion.** `P2` and `P5` are `Option ℚ`-valued and
`none` when `P(L | a) = 0`; `argmaxOpt` ranges over the defined values. This is what every
B/C/D/E fixture does, and it decides A2c (`SealedInfo.lean`), B18 and D1(iii)/D5 downstream.
The 1-at-null variant `P2li` is FAF's `LogicalInduction.conditionalQuote` convention
(`.lake/packages/agentFoundations/LogicalInduction/Properties/Conditioning.lean:67`:
`if V (φ ⋏ ψ) < V ψ then V (φ ⋏ ψ) / V ψ else 1`, junk value `1` at a price-0 condition)
applied indicator-wise to an expectation, which the source registers as ARGUMENT
(NEGATIVES A0; the LI paper's `main.tex:1610` calls the convention "nonstandard" and lets the
reader ignore it). `P2li` is used only in the `_li` variant theorems.

**Ill-posedness recorded (finding 9).** `RUN.md` §2.4 item 3 writes Claude's `D(a)` with the
*unconditional* weight `P^A_n(L)`, which is not defined before the action when `L` depends on
the action; `P5` below (cluster C's action-conditional form) is the only well-typed reading
found in the sources.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- **P1 (cdot, floor 0)** under R1: `∑ s, π s · [leg s a] · V s a a` (`model.py:144-147`).
Void terminals contribute `0` whatever `V` says there: `V` is never read off `leg`.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def P1 (V : MenuVec S A) (a : A) : ℚ := ∑ s, P.prior s * ind (P.leg s a) * V s a a

/-- **P2 (conditioning)** under R1, exclusion convention: `P1 a / P(L | a)`, `none` when
`P(L | a) = 0` (`model.py:150-154`). See the file docstring.
Source: [[corr-legit-neg-2-inventory]] item 2-003
Kind: D
Fidelity: exact -/
def P2 (V : MenuVec S A) (a : A) : Option ℚ :=
  if P.PL a = 0 then none else some (P.P1 V a / P.PL a)

/-- **P2 under the 1-at-null convention** (FAF's `conditionalQuote` junk value, `main.tex:1610`,
applied indicator-wise to an expectation — ARGUMENT in the source, NEGATIVES A0). Used only in
the variant theorems whose names carry `_li`. Not the convention of record.
Source: [[corr-legit-neg-inventory]] item 002; NEGATIVES A0
Kind: D
Fidelity: variant: junk value 1 at a null condition -/
def P2li (V : MenuVec S A) (a : A) : ℚ :=
  if P.PL a = 0 then 1 else P.P1 V a / P.PL a

/-- The identity `P1 a = P(L | a) · P2 a` wherever `P2` is defined (item 002).
Source: [[corr-legit-neg-inventory]] item 002
Kind: L
Fidelity: exact -/
theorem P1_eq_PL_mul_div (V : MenuVec S A) (a : A) (h : P.PL a ≠ 0) :
    P.P1 V a = P.PL a * (P.P1 V a / P.PL a) := by
  field_simp

/-- `P2_of_ne`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P2_of_ne (V : MenuVec S A) (a : A) (h : P.PL a ≠ 0) :
    P.P2 V a = some (P.P1 V a / P.PL a) := by
  simp [P2, h]

/-- `P2_of_eq`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P2_of_eq (V : MenuVec S A) (a : A) (h : P.PL a = 0) : P.P2 V a = none := by
  simp [P2, h]

/-- **P3 (graded)**: `∑ s, π s · ([leg] · V s a a + [¬leg] · λ · W s a a)` with void grades `W`
(C `model.py:70-77`). `λ = 0` recovers P1.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def P3 (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A) (a : A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam * Wg s a a)

/-- `P3_zero`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P3_zero (Wg V : MenuVec S A) (a : A) : P.P3 Wg 0 V a = P.P1 V a := by
  unfold P3 P1
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **P4a (Hausner-lexicographic)**: the pair `(P(L | a), P3 W 1 V a)` compared in `Prod.Lex`
(C `model.py:79-80`). Comparing the *sum* of the pair would not be lexicographic.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def P4a (Wg V : MenuVec S A) (a : A) : ℚ ×ₗ ℚ := toLex (P.PL a, P.P3 Wg 1 V a)

open Classical in
/-- Maximisers of a lexicographically-valued score.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def argmaxLex (f : A → ℚ ×ₗ ℚ) : Finset A := univ.filter fun a => ∀ b, f b ≤ f a

/-- `mem_argmaxLex`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_argmaxLex {f : A → ℚ ×ₗ ℚ} {a : A} : a ∈ argmaxLex f ↔ ∀ b, f b ≤ f a := by
  simp [argmaxLex]

/-- **P4b (cardinal gap)**: `∑ s, π s · ([leg] · (κ + (1 − κ) V s a a) + [¬leg] · κ' · W s a a)`
with `0 ≤ κ' < κ ≤ 1` carried as a hypothesis by the theorems, not baked in (C `model.py:82-90`).
`κ = κ' = 0` is P1.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def P4b (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A) (a : A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s a) * (κ + (1 - κ) * V s a a) + ind (!P.leg s a) * κ' * Wg s a a)

/-- `P4b_zero`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P4b_zero (Wg V : MenuVec S A) (a : A) : P.P4b Wg 0 0 V a = P.P1 V a := by
  unfold P4b P1
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

open Classical in
/-- **P4c (tolerance)**: maximise the grade `P3 W 1 V` among the options whose `P(L | a)` is
within `δ` of the best `P(L | ·)`.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
noncomputable def P4c [Nonempty A] (Wg : MenuVec S A) (δ : ℚ) (V : MenuVec S A) : Finset A :=
  let best := univ.sup' univ_nonempty P.PL
  univ.filter fun a => best - δ ≤ P.PL a ∧
    ∀ b, best - δ ≤ P.PL b → P.P3 Wg 1 V b ≤ P.P3 Wg 1 V a

/-- `K̄ a = (∑_{s ∈ L_a} π s · K s a a) / P(L | a)`: the legitimate humans' average cross-branch
assessment of `a` (C `model.py:92-98`). Junk `… / 0` at `P(L | a) = 0`, where `P5` is `none`.
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def Kbar (K : MenuVec S A) (a : A) : ℚ :=
  (∑ s, P.prior s * ind (P.leg s a) * K s a a) / P.PL a

/-- **P5 (cross-branch decomposition, action-conditional)**: `none` at `P(L | a) = 0`; `P1 a`
at `P(L | a) = 1` (`K` unread — a definition note of item 2-inventory's findings); otherwise
`P1 a + (1 − P(L | a)) · K̄ a` (C `model.py:92-98`). The only well-typed form of `RUN.md` §2.4
item 3's `D(a)` found (finding 9).
Source: [[corr-legit-neg-inventory]] item 002
Kind: D
Fidelity: exact -/
def P5 (K V : MenuVec S A) (a : A) : Option ℚ :=
  if P.PL a = 0 then none
  else if P.PL a = 1 then some (P.P1 V a)
  else some (P.P1 V a + (1 - P.PL a) * P.Kbar K a)

/-- The three-case `P5` is the uniform formula wherever it is defined (the `P(L | a) = 1`
branch only avoids reading `K`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P5_of_ne (K V : MenuVec S A) (a : A) (h : P.PL a ≠ 0) :
    P.P5 K V a = some (P.P1 V a + (1 - P.PL a) * P.Kbar K a) := by
  unfold P5
  rw [if_neg h]
  split_ifs with h1
  · rw [h1]; simp
  · rfl

/-! ### The lottery encoding (cluster D) -/

/-- Cluster D's lottery of action `a`: the pushforward of `(π, leg(·, a), V(·, a)(a))`, one
branch per state (item 2-001's reconciliation).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def lotteryOf (V : MenuVec S A) (a : A) : S → ℚ × Bool × ℚ :=
  fun s => (P.prior s, P.leg s a, V s a a)

end Problem

/-- Cluster D's `cdot` of a lottery: `∑ p · [L] · V` over its branches
(`clusters/D/fixtures/common.py`, item 2-001).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def cdotOfLottery {S : Type} [Fintype S] (l : S → ℚ × Bool × ℚ) : ℚ :=
  ∑ s, (l s).1 * ind (l s).2.1 * (l s).2.2

/-- D's `cdot` of the lottery of `a` is `P1 a`: the two encodings agree (item 2-001).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: L
Fidelity: exact -/
theorem cdotOfLottery_lotteryOf {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)
    (V : MenuVec S A) (a : A) : cdotOfLottery (P.lotteryOf V a) = P.P1 V a := rfl

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-! ### Basic facts about `P1` -/

/-- `P1` is monotone in the diagonal of `V` on legitimate terminals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_mono {V V' : MenuVec S A} (a : A)
    (h : ∀ s, P.leg s a = true → V s a a ≤ V' s a a) : P.P1 V a ≤ P.P1 V' a := by
  unfold P1
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hs : P.leg s a = true
  · simp only [hs, ind_true, mul_one]
    exact mul_le_mul_of_nonneg_left (h s hs) (P.prior_nonneg s)
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- `P1` reads `V` only on legitimate terminals: two vectors agreeing there give the same `P1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_congr {V V' : MenuVec S A} (a : A)
    (h : ∀ s, P.leg s a = true → V s a a = V' s a a) : P.P1 V a = P.P1 V' a :=
  le_antisymm (P.P1_mono a fun s hs => (h s hs).le) (P.P1_mono a fun s hs => (h s hs).ge)

/-- Upper bound: `V ≤ D` on legitimate diagonal terminals gives `P1 V a ≤ D · P(L | a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_le_mul_PL {V : MenuVec S A} {D : ℚ} (a : A)
    (h : ∀ s, P.leg s a = true → V s a a ≤ D) : P.P1 V a ≤ D * P.PL a := by
  unfold P1 PL mass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hs : P.leg s a = true
  · simp only [hs, ind_true, mul_one]
    have := mul_le_mul_of_nonneg_left (h s hs) (P.prior_nonneg s)
    linarith
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- Lower bound: `0 ≤ V` on legitimate diagonal terminals gives `0 ≤ P1 V a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_nonneg {V : MenuVec S A} (a : A) (h : ∀ s, P.leg s a = true → 0 ≤ V s a a) :
    0 ≤ P.P1 V a := by
  unfold P1
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases hs : P.leg s a = true
  · simp only [hs, ind_true, mul_one]; exact mul_nonneg (P.prior_nonneg s) (h s hs)
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- `P1` of `S1 u` at a fully legitimate action is the standard `H` (every terminal of `a` is
legitimate, so the floor never fires).
Source: [[corr-legit-neg-inventory]] item 019 (B6, the identity `P1 = H − E[(1 − ℓ) u]` at `ℓ ≡ 1`)
Kind: L
Fidelity: exact -/
lemma P1_S1_eq_H_of_allLeg (a : A) (h : ∀ s, P.leg s a = true) : P.P1 (S1 P.u) a = P.H a := by
  unfold P1 H W EU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [h s]

/-- The zero-mass case: `P(L | a) = 0` makes `P1 V a = 0` for every `V` (the floor on every
world).
Source: NEGATIVES A0 (the `π(L) = 0` clause)
Kind: L
Fidelity: exact -/
lemma P1_eq_zero_of_PL_eq_zero (V : MenuVec S A) (a : A) (h : P.PL a = 0) : P.P1 V a = 0 := by
  unfold P1
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : P.leg s a = true
  · have := P.prior_eq_zero_of_mass_eq_zero h s hs
    simp [this]
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-! ### The sealed regime's `J₁`, `J₂` -/

/-- `J₁ c = ∑_{s ∈ L} π s · V s c` for a selection-independent vector `V` (NEGATIVES A §0).
Source: [[corr-legit-neg-inventory]] item 002 (display `J₁`)
Kind: D
Fidelity: exact -/
def J1 (ℓ : S → Bool) (V : S → A → ℚ) (c : A) : ℚ := ∑ s, P.prior s * ind (ℓ s) * V s c

/-- `J₂ c = J₁ c / π(L)`, `none` at `π(L) = 0` (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 002 (display `J₂`)
Kind: D
Fidelity: exact -/
def J2 (ℓ : S → Bool) (V : S → A → ℚ) (c : A) : Option ℚ :=
  if P.mass ℓ = 0 then none else some (P.J1 ℓ V c / P.mass ℓ)

/-- Under `SealedBy ℓ`, `P1` of the lifted vector is `J₁`: the sealed displays are the
proposals of record, not a substitute.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_liftV_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (V : S → A → ℚ) (c : A) :
    P.P1 (liftV V) c = P.J1 ℓ V c := by
  unfold P1 J1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [h s c]

/-- `P2_liftV_of_SealedBy`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P2_liftV_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (V : S → A → ℚ) (c : A) :
    P.P2 (liftV V) c = P.J2 ℓ V c := by
  unfold P2 J2
  rw [P.PL_eq_mass_of_SealedBy h, P.P1_liftV_of_SealedBy h]

/-- `J₁` is linear in the vector: `J₁ (V + V') = J₁ V + J₁ V'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma J1_add (ℓ : S → Bool) (V V' : S → A → ℚ) (c : A) :
    P.J1 ℓ (fun s c => V s c + V' s c) c = P.J1 ℓ V c + P.J1 ℓ V' c := by
  unfold J1; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `J1_smul`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma J1_smul (ℓ : S → Bool) (r : ℚ) (V : S → A → ℚ) (c : A) :
    P.J1 ℓ (fun s c => r * V s c) c = r * P.J1 ℓ V c := by
  unfold J1; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- A vector constant in the state gives `J₁ c = π(L) · v c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma J1_const (ℓ : S → Bool) (v : A → ℚ) (c : A) :
    P.J1 ℓ (fun _ c => v c) c = P.mass ℓ * v c := by
  unfold J1 mass; rw [Finset.sum_mul]

end Problem

end Cleanroom.Corrigibility.LegitNegStatic
