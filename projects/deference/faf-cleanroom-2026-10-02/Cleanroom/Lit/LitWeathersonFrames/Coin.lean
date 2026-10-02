import Cleanroom.Lit.LitWeathersonFrames.Ray
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frame Coin (T6): Value fails, Weak Value holds, Total Trust holds

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). Weatherson's **Coin**: a fair
coin is flipped until it lands Tails, `F` the number of flips; world `n : ℕ` is `F = n + 1`,
`π n = (1/2)^(n+1)`; the Experimenter at `F = n + 1` learns `F ≥ n + 1`, so Coin is the ray frame
of the geometric prior (`Ray.lean`). The menu `O i` (`i : ℕ`) is the paper's `O_{i+1}`: value
`2^i` on `{F > i + 1}` (worlds `m > i`), `0` elsewhere — the transcriber's factor-2 repair
(note 3, l. 15: printed `2^{i+1}` gives `E_π(O_i) = 1`, the repaired `2^{i}` gives `1/2`, and
nothing below depends on which). Estimates at world `n`: `E_{P_n}(O j) = 2^n / 2` for `j ≥ n`,
`2^j` for `j < n`, so **every** `O j` with `j ≥ n − 1` is optimal at `n` (recommended strategies
are far from unique — finding F-T6). The paper's strategy `s n = n` has return `0` at every
world; `s'` (choose `O_{n−1}` at `n ∈ {2, 3, 4}`, `O_n` elsewhere) has return `3/4 ≥ 1/2`.
Each `O i` is bounded, the family is not uniformly bounded, and the menu is infinite: by the ray
lemma each of Weatherson's two objections alone restores Value.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset Filter Topology Cleanroom.Found.LitDdbFrames

noncomputable section

namespace Coin

/-- Coin's prior: `π n = (1/2)^(n+1)`, i.e. `π(F = n + 1) = 2^{-(n+1)}`.
Source: [[Deference and Infinite Frames]] §3 l. 188 (`π(F = x) = 2^{-x}`)
Kind: D
Fidelity: exact (world `n` is `F = n + 1`) -/
def π (n : ℕ) : ℝ := (1/2) ^ (n + 1)

/-- Coin's prior is the geometric series `1/2/2^n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_eq : π = fun n => (1:ℝ) / 2 / 2 ^ n := by
  funext n; unfold π; rw [pow_succ, one_div_pow]; ring

/-- Coin's prior is a ray prior (full support, sums to one).
Source: [[Deference and Infinite Frames]] §3 l. 188
Kind: L
Fidelity: n/a -/
theorem isRayPrior : IsRayPrior π :=
  ⟨fun n => by unfold π; positivity, by rw [π_eq]; exact hasSum_geometric_two' 1⟩

/-- **Frame Coin**: the ray frame of the geometric prior.
Source: [[Deference and Infinite Frames]] §3 l. 188 (`P(F = x) = π(· | F ≥ x)`)
Kind: D
Fidelity: exact -/
def frame : CFrame ℕ := rayFrame π isRayPrior

/-- The tail mass of Coin: `π(F ≥ n + 1) = (1/2)^n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tail_eq (n : ℕ) : tail π n = (1/2) ^ n := by
  unfold tail
  have h : HasSum (fun m => π (m + n)) ((1/2) ^ n) := by
    have := (hasSum_geometric_two' 1).mul_left ((1/2 : ℝ) ^ n)
    rw [mul_one] at this
    refine this.congr_fun fun m => ?_
    unfold π; rw [pow_succ, pow_add, one_div_pow]; ring
  exact h.tsum_eq

/-- The option `O i` (the paper's `O_{i+1}`, repaired): `2^i` on worlds `m > i`, else `0`.
Source: [[Deference and Infinite Frames]] §3 l. 188, transcription note 3 (l. 15)
Kind: D
Fidelity: variant: index shifted by one and the transcriber's factor-2 repair (`2^{i}` for the
printed `2^{i+1}`); nothing below depends on the factor -/
def O (i : ℕ) : ℕ → ℝ := fun m => if i < m then (2:ℝ) ^ i else 0

/-- `O i` as a step variable `𝟙[i + 1 ≤ ·] 2^i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem O_eq (i : ℕ) : O i = fun m => if i + 1 ≤ m then (2:ℝ) ^ i else 0 := by
  funext m; unfold O
  by_cases h : i < m
  · simp [h, Nat.lt_iff_add_one_le.mp h]
  · simp [h]

/-- Each `O i` is bounded (by `2^i`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem O_bdd (i : ℕ) : Bdd (O i) :=
  ⟨2 ^ i, fun m => by unfold O; split_ifs <;> simp⟩

/-- The family `O` is **not** uniformly bounded: `|O i (i+1)| = 2^i` is unbounded in `i`.
Source: [[Deference and Infinite Frames]] §3 l. 194 ("the value function … was unbounded")
Kind: L
Fidelity: exact -/
theorem O_not_bddFam : ¬ BddFam O := by
  rintro ⟨M, hM⟩
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt M (by norm_num : (1:ℝ) < 2)
  have := hM i (i + 1)
  simp [O] at this
  linarith

/-- Each `O i` is `π`-integrable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem O_integrable (i : ℕ) : IntegrableW π (O i) := (O_bdd i).integrableW isRayPrior.isDist

/-- Each `O i` is integrated by every row of Coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem O_rows (i : ℕ) : RowsIntegrable frame (O i) := (O_bdd i).rowsIntegrable frame

/-- `E_π(O i) = 1/2` for every `i` (the repaired value; the printed `2^{i+1}` would give `1`).
Source: [[Deference and Infinite Frames]] §3 l. 188 ("`E(o, π) = 1/2`")
Kind: L
Fidelity: exact (repaired) -/
theorem E_prior_O (i : ℕ) : Eℕ π (O i) = 1/2 := by
  have h0 : Eℕ π (O i) = Eℕ (rayP π 0) (O i) := by
    unfold Eℕ
    refine tsum_congr fun m => ?_
    simp [rayP, tail_eq]
  rw [h0, O_eq, rayE_step_of_le isRayPrior (Nat.zero_le _), tail_eq, tail_eq]
  rw [one_div_pow, pow_succ]
  field_simp

/-- Estimates at world `n`, case `n ≤ j`: `E_{P_n}(O j) = 2^n / 2`.
Source: [[Deference and Infinite Frames]] §3 l. 188 ("as can be easily checked"); inventory 032
Kind: L
Fidelity: exact -/
theorem estimate_of_le {n j : ℕ} (h : n ≤ j) : Eℕ (rayP π n) (O j) = 2 ^ n / 2 := by
  rw [O_eq, rayE_step_of_le isRayPrior (by omega), tail_eq, tail_eq]
  rw [one_div_pow, one_div_pow, pow_succ]
  field_simp

/-- Estimates at world `n`, case `j < n`: `E_{P_n}(O j) = 2^j`.
Source: [[Deference and Infinite Frames]] §3 l. 188; inventory 032
Kind: L
Fidelity: exact -/
theorem estimate_of_lt {n j : ℕ} (h : j < n) : Eℕ (rayP π n) (O j) = 2 ^ j := by
  rw [O_eq, rayE_step_of_ge isRayPrior (by omega)]

/-- The optimal value at world `n` is `2^n / 2`, attained exactly by the `O j` with
`j + 1 ≥ n`.
Source: inventory 032 (the non-uniqueness of recommended strategies)
Kind: L
Fidelity: exact -/
theorem estimate_le (n j : ℕ) : Eℕ (rayP π n) (O j) ≤ 2 ^ n / 2 := by
  rcases le_or_gt n j with h | h
  · rw [estimate_of_le h]
  · rw [estimate_of_lt h]
    have : (2:ℝ) ^ j * 2 ≤ 2 ^ n := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) h
    linarith

/-- The paper's strategy: at `F = n + 1` choose `O n` (the paper's `s(F = i) = O_i`).
Source: [[Deference and Infinite Frames]] §3 l. 188
Kind: D
Fidelity: exact -/
def s (n : ℕ) : ℕ := n

/-- The paper's strategy is recommended.
Source: [[Deference and Infinite Frames]] §3 l. 188 ("is recommended, as can be easily checked")
Kind: L
Fidelity: exact -/
theorem s_recommended : RecommendedC frame O s :=
  ⟨rayFrame_isStrategy isRayPrior s, fun n j => by
    show Eℕ (rayP π n) (O j) ≤ Eℕ (rayP π n) (O n)
    rw [estimate_of_le le_rfl]; exact estimate_le n j⟩

/-- The paper's strategy returns `0` at every world, so its expected return is `0`.
Source: [[Deference and Infinite Frames]] §3 l. 188 ("`E(s) = 0`")
Kind: L
Fidelity: exact -/
theorem stratValue_s : stratValueC π O s = 0 := by
  unfold stratValueC
  simp [O, s]

/-- **T6 (load-bearing 4). Value fails on Coin**: the paper's recommended strategy `s` has
(summable, indeed zero) return `0 < 1/2 = E_π(O j)`.
Source: [[Deference and Infinite Frames]] §3 l. 188 ("So Value fails on Coin"); inventory 032
Kind: N+
Fidelity: exact (`ValueInt`: any menu, integrable options; the refuting return is summable)
Hyps: none -/
theorem not_valueInt : ¬ ValueInt π frame := by
  intro h
  have := h ℕ O O_integrable O_rows s s_recommended (by simp [O, s]) 0
  rw [E_prior_O, stratValue_s] at this
  norm_num at this

/-- The alternative strategy: `O_{n−1}` at `n ∈ {2, 3, 4}` (the paper's `F ∈ {3, 4, 5}`), `O_n`
elsewhere.
Source: mandate T6 (Weak Value witness); inventory 032
Kind: D
Fidelity: n/a -/
def s' (n : ℕ) : ℕ := if n = 2 ∨ n = 3 ∨ n = 4 then n - 1 else n

/-- The alternative strategy is recommended (`O_{n−1}` is also optimal at `n`).
Source: inventory 032
Kind: L
Fidelity: exact -/
theorem s'_recommended : RecommendedC frame O s' := by
  refine ⟨rayFrame_isStrategy isRayPrior s', fun n j => ?_⟩
  show Eℕ (rayP π n) (O j) ≤ Eℕ (rayP π n) (O (s' n))
  refine le_trans (estimate_le n j) (le_of_eq ?_)
  unfold s'
  split_ifs with h
  · rw [estimate_of_lt (by omega)]
    rcases h with rfl | rfl | rfl <;> norm_num
  · rw [estimate_of_le le_rfl]

/-- The alternative strategy's return is `3/4`: `2^{n−1}` at `n ∈ {2, 3, 4}`, each weighted
`2^{-(n+1)}`, `0` elsewhere.
Source: mandate T6
Kind: L
Fidelity: exact -/
theorem stratValue_s' : stratValueC π O s' = 3/4 := by
  unfold stratValueC
  rw [tsum_eq_sum (s := {2, 3, 4})]
  · simp [O, s', π]; norm_num
  · intro n hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    simp [O, s', hn]

/-- The alternative strategy's return is summable (finitely supported).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem s'_summable : Summable (fun n => π n * O (s' n) n) := by
  refine summable_of_ne_finset_zero (s := {2, 3, 4}) fun n hn => ?_
  simp only [mem_insert, mem_singleton, not_or] at hn
  simp [O, s', hn]

/-- **T6. Weak Value holds on Coin's menu**: the recommended strategy `s'` has summable return
`3/4 ≥ 1/2 = E_π(O j)` for every `j`. (The instance on the menu `O`, not the full predicate
`WeakValueInt`.)
Source: inventory 032 (the Weak-Value observation); mandate T6
Kind: N+
Fidelity: exact (instance on the menu `O`)
Hyps: none -/
theorem weakValue_menu :
    ∃ S, RecommendedC frame O S ∧ Summable (fun n => π n * O (S n) n) ∧
      ∀ j, Eℕ π (O j) ≤ stratValueC π O S :=
  ⟨s', s'_recommended, s'_summable, fun j => by rw [E_prior_O, stratValue_s']; norm_num⟩

/-- **Coin is totally trusted** (integrable variables) — the ray lemma at the geometric prior.
Source: [[Deference and Infinite Frames]] §3 ll. 190–192; inventory 031
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem totalTrustInt : TotalTrustInt π frame := ray_totalTrustInt isRayPrior

/-- **Coin is totally trusted** (bounded variables).
Source: [[Deference and Infinite Frames]] §3 ll. 190–192; inventory 031
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem totalTrustC : TotalTrustC π frame := ray_totalTrustC isRayPrior

/-- **Coin is Valued on finite menus of integrable options** — Weatherson's second objection
(`O` infinite) alone restores Value.
Source: [[Deference and Infinite Frames]] §3 l. 194; mandate T7/T8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem valueFinInt : ValueFinInt π frame := ray_valueFinInt isRayPrior

/-- **Coin is Valued on every uniformly bounded menu** — Weatherson's first objection (unbounded
utilities) alone restores Value.
Source: [[Deference and Infinite Frames]] §3 l. 194; mandate T7/T8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem valueBdd : ValueBdd π frame := ray_valueBdd isRayPrior

/-- **The Coin finding (T6, composite).** Total Trust holds and Value fails on Coin, *and* the
failure needs both an infinite menu and non-uniformly-bounded options: Coin is Valued on every
finite menu of integrable options and on every uniformly bounded menu; Weak Value holds on the
paper's menu. Coin's options are each bounded but not uniformly.
Source: [[Deference and Infinite Frames]] §3 ll. 188–194; abstract l. 29; inventory 031, 032
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem status :
    TotalTrustInt π frame ∧ ¬ ValueInt π frame ∧ ValueFinInt π frame ∧ ValueBdd π frame ∧
      (∃ S, RecommendedC frame O S ∧ Summable (fun n => π n * O (S n) n) ∧
        ∀ j, Eℕ π (O j) ≤ stratValueC π O S) ∧ (∀ i, Bdd (O i)) ∧ ¬ BddFam O :=
  ⟨totalTrustInt, not_valueInt, valueFinInt, valueBdd, weakValue_menu, O_bdd, O_not_bddFam⟩

end Coin

/-! ## A non-geometric ray prior (witness that the geometric weights are not used) -/

namespace Ray23

/-- The prior `π n = (2/3)(1/3)^n`.
Source: mandate T8 (witness)
Kind: D
Fidelity: n/a -/
def π (n : ℕ) : ℝ := 2/3 * (1/3) ^ n

/-- `π` is a ray prior.
Source: mandate T8 (witness)
Kind: N+
Fidelity: n/a -/
theorem isRayPrior : IsRayPrior π := by
  refine ⟨fun n => by unfold π; positivity, ?_⟩
  have := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num)).mul_left (2/3)
  norm_num at this
  exact this

/-- The ray lemma at a non-geometric prior: totally trusted, Valued on finite menus and on
uniformly bounded menus.
Source: mandate T8 (witness: the geometric weights are not used)
Kind: N+
Fidelity: n/a -/
theorem status :
    TotalTrustInt π (rayFrame π isRayPrior) ∧ ValueFinInt π (rayFrame π isRayPrior) ∧
      ValueBdd π (rayFrame π isRayPrior) :=
  ⟨ray_totalTrustInt _, ray_valueFinInt _, ray_valueBdd _⟩

end Ray23

end

end Cleanroom.Lit.LitWeathersonFrames
