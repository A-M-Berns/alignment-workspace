import Cleanroom.Corrigibility.CorrPowerChannel.Power
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

/-!
# `corr-power-channel` — T7(a),(c),(d): Turner's scaling law as an orbit count; erosion is
POWER-seeking one-shot

**"Typically optimal" is an orbit count, not a probability** (Turner et al. 2021 Definition 6.5):
every statement below is a cardinality inequality over the orbit `{R ∘ σ | σ ∈ Perm S}` of one
reward vector, never "with probability ≥ 1/2".

* `StrictBest R T x`: `x ∈ T` is the strict maximum of `R` on `T`; `strictBestPerms R T x` is the
  set of permutations `σ` for which `x` is strictly best under `R ∘ σ` on `T`.
* `card_strictBestPerms_eq` (the symmetry): `σ ↦ σ · swap x₀ x` is a bijection between the
  `x₀`-set and the `x`-set for `x₀, x ∈ T`; `strictBestPerms_disjoint`: a strict maximum is unique.
* **The scaling law** `scaling_law`: `#T · #(strictBestPerms R T x₀) ≤ #(Perm S)` — for
  `S = Fin (n+1)`, `T = univ`: `#{σ | x₀ strictly best under R ∘ σ} ≤ n!` (`scaling_law_fin`),
  "allowing correction is strictly optimal for at most `1/(n+1)` of the permutations of every
  reward function", with **equality iff `R` has a unique maximum** (`scaling_law_fin_eq_iff`).
* **Erosion is POWER-seeking, one-shot, every `D`**: `powerGrip D V B Γ hum` is the POWER of an
  agent whose grip-landing replaces it by the humans' option `hum ∈ B` with probability `Γ`;
  `powerGrip_le_power` (`0 ≤ Γ`), strict iff `Γ > 0` and the humans' option is not
  `D`-a.s. attainable-optimal (`powerGrip_lt_power_iff`).
* **Under an injective reward the scaling law is an equality** (repair round 2):
  `card_strictBestPerms_mul_of_injective`, `#T · #cell(x₀) = #Perm S` for any `T ∋ x₀` — the cells
  cover the group (`exists_strictBestPerms_of_injective`); this is what makes the MDP's keep cell
  exactly one third of the orbit (`Mdp.lean`, `card_keepOptPerms`).
* **Turner's results apply to the mixture** (106(a),(c)): `scaling_law_mixValue` instantiates the
  scaling law at `R := mixValue P V` — a remark made exact, not a new theorem.

Sources: Turner 2021 "VNM-incoherent" l. 55–65 (the letter gridworld, the `1/(n+1)` bound);
Turner et al. 2021 Def. 6.3–6.5 (orbits, `≥_most`); channel-final.md S9/P7 (l. 81, 103, the blind
form `POWER^Γ`); power-wisdom-final.md S4(a),(c) (l. 107).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

section Orbit

variable {S : Type} [Fintype S] [DecidableEq S]

/-- `x` is the **strict maximum of `R` on `T`**: `x ∈ T` and `R y < R x` for every other `y ∈ T`.
Source: Turner 2021 "VNM-incoherent" l. 61 ("strictly optimal"); Turner et al. 2021 Def. 6.5
Kind: D
Fidelity: exact -/
def StrictBest (R : S → ℝ) (T : Finset S) (x : S) : Prop := x ∈ T ∧ ∀ y ∈ T, y ≠ x → R y < R x

open Classical in
/-- **The orbit cell**: the permutations `σ` for which `x` is strictly best under `R ∘ σ` on `T` —
the orbit of `R` is `{R ∘ σ}`, and this is the cell of the orbit where "`x` is strictly
optimal" (Definition 6.5's counting set).
Source: Turner et al. 2021 Def. 6.4–6.5 (l. 190); "VNM-incoherent" l. 61
Kind: D
Fidelity: exact (one reward vector's orbit, as a `Finset (Perm S)`) -/
def strictBestPerms (R : S → ℝ) (T : Finset S) (x : S) : Finset (Equiv.Perm S) :=
  univ.filter (fun σ => StrictBest (R ∘ σ) T x)

open Classical in
/-- Membership in the orbit cell. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mem_strictBestPerms {R : S → ℝ} {T : Finset S} {x : S} {σ : Equiv.Perm S} :
    σ ∈ strictBestPerms R T x ↔ StrictBest (R ∘ σ) T x := by
  simp [strictBestPerms]

/-- Right-multiplying by `swap x₀ x` moves the `x₀`-cell into the `x`-cell.
Source: Turner 2021 "VNM-incoherent" l. 61 (the scaling-law symmetry); [[corr-power-channel-mandate]]
T7(a) ("the map `σ ↦ σ ∘ (x₀ x)`")
Kind: L
Fidelity: n/a -/
theorem strictBest_mul_swap {R : S → ℝ} {T : Finset S} {x₀ x : S} (hx : x ∈ T)
    {σ : Equiv.Perm S} (h : StrictBest (R ∘ σ) T x₀) :
    StrictBest (R ∘ (σ * Equiv.swap x₀ x)) T x := by
  refine ⟨hx, fun y hy hyx => ?_⟩
  simp only [Function.comp, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hmem : Equiv.swap x₀ x y ∈ T := by
    by_cases hyx₀ : y = x₀
    · rw [hyx₀, Equiv.swap_apply_left]; exact hx
    · rw [Equiv.swap_apply_of_ne_of_ne hyx₀ hyx]; exact hy
  have hne : Equiv.swap x₀ x y ≠ x₀ := by
    intro hc
    apply hyx
    exact (Equiv.swap x₀ x).injective (hc.trans (Equiv.swap_apply_right x₀ x).symm)
  exact h.2 _ hmem hne

open Classical in
/-- **The symmetry of the orbit count**: every cell has the same size — `σ ↦ σ · swap x₀ x` is a
bijection from the `x₀`-cell to the `x`-cell (its own inverse).
Source: Turner 2021 "VNM-incoherent" l. 61; Turner et al. 2021 Lemma E.24's symmetry
Kind: P
Fidelity: exact
Hyps: (a) `x₀, x ∈ T` -/
theorem card_strictBestPerms_eq (R : S → ℝ) {T : Finset S} {x₀ x : S} (hx₀ : x₀ ∈ T)
    (hx : x ∈ T) : (strictBestPerms R T x₀).card = (strictBestPerms R T x).card := by
  refine card_bij' (fun σ _ => σ * Equiv.swap x₀ x) (fun τ _ => τ * Equiv.swap x₀ x) ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_strictBestPerms] at hσ ⊢
    exact strictBest_mul_swap hx hσ
  · intro τ hτ
    rw [mem_strictBestPerms] at hτ ⊢
    have := strictBest_mul_swap hx₀ hτ
    rwa [Equiv.swap_comm] at this
  · intro σ _
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one]
  · intro τ _
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one]

open Classical in
/-- **A strict maximum is unique**: the cells of distinct `x ≠ x'` are disjoint.
Source: none: infrastructure (Definition 6.5's counting sets are disjoint)
Kind: L
Fidelity: n/a -/
theorem strictBestPerms_disjoint (R : S → ℝ) (T : Finset S) {x x' : S} (hne : x ≠ x') :
    Disjoint (strictBestPerms R T x) (strictBestPerms R T x') := by
  rw [disjoint_left]
  intro σ h h'
  rw [mem_strictBestPerms] at h h'
  have h1 := h.2 x' h'.1 (Ne.symm hne)
  have h2 := h'.2 x h.1 hne
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

open Classical in
/-- **The scaling law, general form**: `#T · #{σ | x₀ strictly best under R ∘ σ on T} ≤ #Perm S`
for `x₀ ∈ T` — the `#T` equal-sized disjoint cells fit inside the symmetric group.
Source: Turner 2021 "VNM-incoherent" l. 61–65 ("at most `1/(n+1)` of the permutations");
[[corr-power-channel-mandate]] T7(a)
Kind: P
Fidelity: exact (cardinality form; `T` any subset containing `x₀`, so the MDP count is a special case)
Hyps: (a) `x₀ ∈ T` -/
theorem scaling_law (R : S → ℝ) {T : Finset S} {x₀ : S} (hx₀ : x₀ ∈ T) :
    T.card * (strictBestPerms R T x₀).card ≤ Fintype.card (Equiv.Perm S) := by
  have hsum : ∑ x ∈ T, (strictBestPerms R T x).card = T.card * (strictBestPerms R T x₀).card := by
    rw [sum_congr rfl (fun x hx => (card_strictBestPerms_eq R hx hx₀)), sum_const, smul_eq_mul]
  rw [← hsum, ← card_biUnion (fun x _ y _ hxy => strictBestPerms_disjoint R T hxy)]
  exact card_le_univ _

/-- **The scaling law on `Fin (n+1)`**: for every reward vector `R` and target `x₀`, allowing
correction (`x₀` strictly best) is strictly optimal for at most `n!` of the `(n+1)!`
permutations — a `1/(n+1)` share, as an exact count.
Source: Turner 2021 "VNM-incoherent" l. 65 ("allowing correction will be strictly optimal for at
most `1/(n+1)` of the permutations of every reward function")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem scaling_law_fin (n : ℕ) (R : Fin (n + 1) → ℝ) (x₀ : Fin (n + 1)) :
    (strictBestPerms R univ x₀).card ≤ n.factorial := by
  have h := scaling_law R (T := univ) (x₀ := x₀) (mem_univ _)
  rw [card_univ, Fintype.card_fin, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.succ_pos n)

open Classical in
/-- **Under an injective reward every permutation lies in some cell of `T`**: `R ∘ σ` has a strict
maximum on a nonempty `T` for every `σ` (a maximum exists, and injectivity makes it strict), so the
cells `{strictBestPerms R T x | x ∈ T}` cover `Perm S`. The covering step of
`scaling_law_fin_eq_iff`'s `⇐`, for an arbitrary `T`.
Source: none: infrastructure ([[corr-power-channel-audit-r2-fidelity]] B1, the covering lemma)
Kind: L
Fidelity: n/a -/
theorem exists_strictBestPerms_of_injective (R : S → ℝ) (hR : Function.Injective R)
    {T : Finset S} (hT : T.Nonempty) (σ : Equiv.Perm S) : ∃ x ∈ T, σ ∈ strictBestPerms R T x := by
  obtain ⟨x, hx, hmax⟩ := T.exists_max_image (R ∘ σ) hT
  refine ⟨x, hx, ?_⟩
  rw [mem_strictBestPerms]
  refine ⟨hx, fun y hy hne => lt_of_le_of_ne (hmax y hy) ?_⟩
  intro hc
  exact hne (σ.injective (hR hc))

open Classical in
/-- **The scaling law is an equality under an injective reward**: `#T · #cell(x₀) = #Perm S` for
`x₀ ∈ T` — the `#T` equal, disjoint cells cover the group, so each is exactly a `1/#T` share of
the permutations. The `Fin`/`univ` case is `scaling_law_fin_eq_iff`'s `⇐`; this is the general `T`.
Source: Turner 2021 "VNM-incoherent" l. 61–65 (the "at most `1/(n+1)`" attained);
[[corr-power-channel-audit-r2-fidelity]] B1
Kind: P
Fidelity: stronger: equality for any `T ∋ x₀` under injectivity (the source states "at most")
Hyps: (a) `R` injective, `x₀ ∈ T` -/
theorem card_strictBestPerms_mul_of_injective (R : S → ℝ) (hR : Function.Injective R)
    {T : Finset S} {x₀ : S} (hx₀ : x₀ ∈ T) :
    T.card * (strictBestPerms R T x₀).card = Fintype.card (Equiv.Perm S) := by
  have hsum : ∑ x ∈ T, (strictBestPerms R T x).card = T.card * (strictBestPerms R T x₀).card := by
    rw [sum_congr rfl (fun x hx => (card_strictBestPerms_eq R hx hx₀)), sum_const, smul_eq_mul]
  have hcover : T.biUnion (strictBestPerms R T) = univ := by
    apply eq_univ_of_forall
    intro σ
    rw [mem_biUnion]
    exact exists_strictBestPerms_of_injective R hR ⟨x₀, hx₀⟩ σ
  rw [← hsum, ← card_biUnion (fun x _ y _ hxy => strictBestPerms_disjoint R T hxy), hcover,
    card_univ]

open Classical in
/-- A nonempty cell exhibits a unique maximum of `R`: if `x₀` is strictly best under `R ∘ σ`, then
`σ x₀` is the unique maximum of `R` (the `⇒` half of `scaling_law_fin_eq_iff`, which needs only
`0 < #cell`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem unique_max_of_cell_pos (n : ℕ) (R : Fin (n + 1) → ℝ) (x₀ : Fin (n + 1))
    (hpos : 0 < (strictBestPerms R univ x₀).card) : ∃ m, ∀ y, y ≠ m → R y < R m := by
  obtain ⟨σ, hσ⟩ := card_pos.1 hpos
  rw [mem_strictBestPerms] at hσ
  refine ⟨σ x₀, fun y hy => ?_⟩
  have := hσ.2 (σ.symm y) (mem_univ _) (by
    intro hc
    apply hy
    rw [← σ.apply_symm_apply y, hc])
  simpa using this

open Classical in
/-- **The scaling law's equality case: `#cell(x₀) = n!` iff `R` has a unique maximum.** If some `σ`
makes `x₀` strictly best then `R` has a unique maximum (its image); conversely a unique maximum
`m` makes `σ⁻¹ m` strictly best under `R ∘ σ` for every `σ`, so the `n+1` cells partition the
group.
Source: Turner 2021 "VNM-incoherent" l. 61–65 (the "at most" is attained exactly when the reward
vector has a unique top state)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem scaling_law_fin_eq_iff (n : ℕ) (R : Fin (n + 1) → ℝ) (x₀ : Fin (n + 1)) :
    (strictBestPerms R univ x₀).card = n.factorial ↔ ∃ m, ∀ y, y ≠ m → R y < R m := by
  constructor
  · intro h
    exact unique_max_of_cell_pos n R x₀ (by rw [h]; exact Nat.factorial_pos n)
  · rintro ⟨m, hm⟩
    -- every σ lies in the cell of `σ⁻¹ m`
    have hcover : (univ : Finset (Fin (n + 1))).biUnion (strictBestPerms R univ) = univ := by
      apply eq_univ_of_forall
      intro σ
      rw [mem_biUnion]
      refine ⟨σ.symm m, mem_univ _, ?_⟩
      rw [mem_strictBestPerms]
      refine ⟨mem_univ _, fun y _ hy => ?_⟩
      simp only [Function.comp, Equiv.apply_symm_apply]
      apply hm
      intro hc
      apply hy
      rw [← hc, Equiv.symm_apply_apply]
    have hsum : ∑ x, (strictBestPerms R univ x).card = (n + 1) * (strictBestPerms R univ x₀).card := by
      rw [sum_congr rfl (fun x _ => (card_strictBestPerms_eq R (mem_univ x) (mem_univ x₀))),
        sum_const, smul_eq_mul, card_univ, Fintype.card_fin]
    have htot : ∑ x, (strictBestPerms R univ x).card = (n + 1).factorial := by
      rw [← card_biUnion (fun x _ y _ hxy => strictBestPerms_disjoint R univ hxy), hcover,
        card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [hsum, Nat.factorial_succ] at htot
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) htot

open Classical in
/-- **The cell is nonempty iff `R` has a unique maximum** — with `scaling_law_fin_eq_iff`, the cell
of `x₀` is either empty or exactly a `1/(n+1)` share of the permutations, so the source's "at most
`1/(n+1)`" is exact in both directions.
Source: Turner 2021 "VNM-incoherent" l. 61–65; [[corr-power-channel-audit-r1-fidelity]] N9
Kind: P
Fidelity: stronger: the dichotomy behind the source's "at most"
Hyps: (a) none -/
theorem scaling_law_fin_pos_iff (n : ℕ) (R : Fin (n + 1) → ℝ) (x₀ : Fin (n + 1)) :
    0 < (strictBestPerms R univ x₀).card ↔ ∃ m, ∀ y, y ≠ m → R y < R m :=
  ⟨unique_max_of_cell_pos n R x₀, fun h => by
    rw [(scaling_law_fin_eq_iff n R x₀).2 h]; exact Nat.factorial_pos n⟩

open Classical in
/-- **The dichotomy**: the cell of `x₀` has `0` or exactly `n!` permutations.
Source: Turner 2021 "VNM-incoherent" l. 61–65
Kind: C
Fidelity: stronger: the source states only "at most"
Hyps: (a) none -/
theorem scaling_law_fin_dichotomy (n : ℕ) (R : Fin (n + 1) → ℝ) (x₀ : Fin (n + 1)) :
    (strictBestPerms R univ x₀).card = 0 ∨ (strictBestPerms R univ x₀).card = n.factorial := by
  rcases Nat.eq_zero_or_pos (strictBestPerms R univ x₀).card with h | h
  · exact Or.inl h
  · exact Or.inr ((scaling_law_fin_eq_iff n R x₀).2 ((scaling_law_fin_pos_iff n R x₀).1 h))

end Orbit

/-! ## (c) Erosion is POWER-seeking, one-shot, every `D` -/

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω]

/-- **POWER under a grip** (channel-final S9's displayed "general form", value-certain): with
probability `Γ` the humans' landing replaces the agent's choice by their option `hum` *in every
world*; otherwise the agent attains the best of `B`.
`POWER^Γ_D(B) = (1 − Γ)·POWER_D(B) + Γ·E_D[V_ω(hum)]`. The free arm is `POWER` (the maximum inside
the expectation — the value-certain attainable value), not the blind free arm `(E_P X)⁺` of
`Grip.lean`; the two agree only for a point-mass `D`, which is the source's own "for a
value-certain agent" caveat (F-18). The source's label "general form for the blind model" is
therefore a misnomer for this formula.
Source: channel-final.md S9 (l. 81, "General form for the blind model"), P7 (l. 103)
Kind: D
Fidelity: exact (to the formula as displayed) -/
def powerGrip (D : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) (Γ : ℝ) (hum : A) :
    ℝ :=
  (1 - Γ) * power D V B hB + Γ * expect D (fun ω => V ω hum)

/-- `POWER − POWER^Γ = Γ · (POWER − E_D[V(hum)])`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem power_sub_powerGrip (D : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) (Γ : ℝ)
    (hum : A) :
    power D V B hB - powerGrip D V B hB Γ hum = Γ * (power D V B hB - expect D (fun ω => V ω hum)) := by
  unfold powerGrip; ring

/-- **Erosion is POWER-seeking, one-shot, for every reference distribution** (value-certain form):
removing the grip (`Γ → 0`) weakly raises POWER — `POWER^Γ_D(B) ≤ POWER_D(B)` for `hum ∈ B` and
every `0 ≤ Γ` (`Γ ≤ 1` is not needed). The orbit-count form in the five-state MDP is `Mdp.lean`;
the strict instance on R1's kernel (slope `−9/10`) is `powerGrip_r1_strict` (`Witnesses.lean`).
Source: channel-final.md S10 (l. 83, "Erosion is POWER-seeking"), S9/P7 (l. 81, 103, "for a
value-certain agent the slope is `≤ 0`"); [[corr-power-channel-mandate]] load-bearing 4
Kind: L
Fidelity: exact (one-shot, value-certain form)
Hyps: (a) `hum ∈ B`, `0 ≤ Γ` -/
theorem powerGrip_le_power (D : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) {Γ : ℝ}
    (hΓ : 0 ≤ Γ) {hum : A} (hhum : hum ∈ B) : powerGrip D V B hB Γ hum ≤ power D V B hB := by
  have := mixValue_le_power D V hB hhum
  unfold mixValue at this
  rw [← sub_nonneg, power_sub_powerGrip]
  exact mul_nonneg hΓ (by linarith)

/-- **Strictness**: `POWER^Γ < POWER` iff `Γ > 0` and the humans' option is not `D`-expected
attainable-optimal (`E_D[V(hum)] < POWER_D(B)`). Equality holds iff `Γ = 0` or `hum` attains
the best of `B` `D`-almost surely (the equality `E_D[V(hum)] = E_D[AV_B]` with `V(hum) ≤ AV_B`
pointwise).
Source: channel-final.md S9 (l. 81, "slope `0` where … `≤ 0` where …"); [[corr-power-channel-mandate]]
T16 (the characterization)
Kind: L
Fidelity: exact
Hyps: (a) `hum ∈ B`, `0 ≤ Γ` -/
theorem powerGrip_lt_power_iff (D : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) {hum : A} (hhum : hum ∈ B) :
    powerGrip D V B hB Γ hum < power D V B hB ↔
      0 < Γ ∧ expect D (fun ω => V ω hum) < power D V B hB := by
  have hle := mixValue_le_power D V hB hhum
  unfold mixValue at hle
  rw [← sub_pos, power_sub_powerGrip]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hΓ with h0 | h0
      · exact h0
      · rw [← h0, zero_mul] at h; exact absurd h (lt_irrefl _)
    · by_contra hc
      push Not at hc
      have : power D V B hB - expect D (fun ω => V ω hum) = 0 := by linarith
      rw [this, mul_zero] at h
      exact lt_irrefl _ h
  · rintro ⟨h0, h1⟩
    exact mul_pos h0 (by linarith)

/-- **The characterization of equality** (T16's one-shot half): `POWER^Γ = POWER` iff `Γ = 0` or
`E_D[V(hum)] = POWER_D(B)`.
Source: [[corr-power-channel-mandate]] T16 ("equality iff `Γ = 0` or `V · hum` attains
`attainable` `D`-a.s.")
Kind: L
Fidelity: exact (the `D`-a.s. reading is the expectation equality under the pointwise bound)
Hyps: (a) `hum ∈ B`, `0 ≤ Γ` -/
theorem powerGrip_eq_power_iff (D : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) {hum : A} (hhum : hum ∈ B) :
    powerGrip D V B hB Γ hum = power D V B hB ↔
      Γ = 0 ∨ expect D (fun ω => V ω hum) = power D V B hB := by
  have hle := powerGrip_le_power D V hB hΓ hhum
  have hlt := powerGrip_lt_power_iff D V hB hΓ hhum
  have hle' := mixValue_le_power D V hB hhum
  unfold mixValue at hle'
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : powerGrip D V B hB Γ hum < power D V B hB :=
      hlt.2 ⟨lt_of_le_of_ne hΓ (Ne.symm hc.1), lt_of_le_of_ne hle' hc.2⟩
    rw [h] at this
    exact lt_irrefl _ this
  · rintro (h | h)
    · unfold powerGrip; rw [h]; ring
    · unfold powerGrip; rw [h]; ring

/-! ## (d) Turner's results apply to the mixture -/

/-- **106(a),(c): the mixture is a bounded reward on options and the scaling law applies to it as
to any reward vector** — the instantiation of `scaling_law` at `R := mixValue P V`: for `a₀ ∈ T`,
`#T · #{σ : Perm A | a₀ strictly best under V̄ ∘ σ on T} ≤ #Perm A`. A remark made exact; no
new content beyond `scaling_law`.
Source: power-wisdom-final.md S4(a),(c) (l. 107, "Turner's orbit results apply to its
relabellings"); P3 (l. 163); corr-wf14-106(a),(c)
Kind: L
Fidelity: exact (one-shot: the orbit is over relabellings of the option set)
Hyps: (a) `a₀ ∈ T` -/
theorem scaling_law_mixValue (P : Distr Ω) (V : Ω → A → ℝ) {T : Finset A} {a₀ : A}
    (ha₀ : a₀ ∈ T) :
    T.card * (strictBestPerms (mixValue P V) T a₀).card ≤ Fintype.card (Equiv.Perm A) :=
  scaling_law (mixValue P V) ha₀

end

end Cleanroom.Corrigibility.CorrPowerChannel
