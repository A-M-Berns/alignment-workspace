import Cleanroom.Bli.BliExactness.Liar

/-!
# Audit r3 (adversarial) probe — the interval predicate over every sentence has no positive
world-mixture inhabitant on any family with a persistent cell inside `[0, 1)`; the liar's
interval failure extends to straddling cells

Imports `Cleanroom.Bli.BliExactness.Liar` (Construction level). Not imported by the library.

* `decided_fails_interval` — the interval analogue of `Defs.lean`'s `decided_fails_midpoint`:
  under theory-respect, a `𝒲`-decided sentence fails interval-exactness at every cell `(lo, hi]`
  with `0 ≤ lo` and `hi < 1` of positive mass (its conditional is `0` or `1`, and the cell
  contains neither). `⊤`'s instance is the package's `top_fails_below_cell`; the liar's instance
  is `liar_fails_interval_any_cell` — **no one-sidedness needed**. So the sentence "the interval
  claim does not extend to straddling cells" (findings F6, report decision 2, the docstring of
  `liar_midpoint_fails_any_cell`) is false for straddling cells with `0 ≤ lo`, `hi < 1`: the claim
  extends there, by the decided-sentence mechanism every decided sentence shares
  (`liar_fails_interval_straddling`: `p = ½`, cell `(¼, ¾]`).
* `mixtureHistory`, `mixture_cell_mass` — a finite world mixture gives a cell strictly around the
  paper quote its total mass (all completed-theory worlds hold the cell).
* `exists_liar_quote_interior` — from the package's `lia_liar_asymptotic` (FAF's `thm:lp`): for a
  cell `0 ≤ lo < hi < 1` and every `n`, the liar at threshold `(lo + hi)/2` has its day-`m` quote
  strictly inside the cell at some `m > n`.
* `no_mixture_exactReflectionInterval`, `no_pointWorld_exactReflectionInterval` — **the package's
  prose OPEN ("a coherent inhabitant of the interval-form self-trust predicate over every
  sentence"), answered negatively** for every family that contains a fixed cell `(lo, hi]` with
  `0 ≤ lo < hi < 1` on every day (`x3Cells`; any fixed-resolution dyadic partition of `(0, 1]` at
  resolution `≥ 1`): no finite mixture of completed-theory worlds of `paperDP T` with positive
  total mass satisfies `ExactReflectionInterval (quoteAt T) cells`, for `𝗜𝚺₁ ⪯ T` consistent. The
  refutation uses only `thm:lp` — not "a day-`m` incoherence of the LIA that FAF does not provide"
  (report § Open). What remains open is the case of families whose every cell reaches `1` or
  below `0` (e.g. the single cell `(0, 1]`), and growing-resolution families (Soto's actual
  `2^{-(k+1)}` cells), where the argument needs the liar's quote to avoid cell boundaries.
-/

namespace Cleanroom.Bli.BliExactness.AuditR3

open LogicalInduction LO.Propositional Finset Filter Topology
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliExactness

/-- **The interval analogue of `decided_fails_midpoint`**: under theory-respect, a `𝒲`-decided
sentence fails interval-exactness at every cell with `0 ≤ lo` and `hi < 1` of positive mass. -/
theorem decided_fails_interval (𝒲 : PCWorld → Prop) (ψ χ : Sentence) (p : Sentence → ℝ)
    (hdec : (∀ v : PCWorld, 𝒲 v → v.Holds ψ) ∨ (∀ v : PCWorld, 𝒲 v → ¬ v.Holds ψ))
    {lo hi : ℚ} (hlo : 0 ≤ lo) (hhi : hi < 1)
    (hresp : RespectsEntailment 𝒲 p ψ χ) (hpos : 0 < p χ) :
    ¬ ((lo : ℝ) * p χ < p (ψ ⋏ χ) ∧ p (ψ ⋏ χ) ≤ (hi : ℝ) * p χ) := by
  have hloR : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (hi : ℝ) < 1 := by exact_mod_cast hhi
  rcases decided_conditional 𝒲 ψ χ p hdec hresp with h | h
  · rw [h]
    rintro ⟨-, h2⟩
    nlinarith [mul_pos hpos (sub_pos.2 hhiR)]
  · rw [h]
    rintro ⟨h1, -⟩
    nlinarith [mul_nonneg hloR hpos.le]

/-- A finite mixture of worlds as a history (constant in the day). -/
noncomputable def mixtureHistory {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ) : History :=
  fun _ ψ => ∑ i, w i * (W i).payout ψ

section Cells

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [𝗥₀ ⪯ T]

/-- The liar fails interval-exactness at **every** cell `(lo, hi]` with `0 ≤ lo`, `hi < 1` of
positive mass under theory-respect — straddling cells included; the `hside` hypothesis of
`exact_reflection_fails_liar` is not needed there. -/
theorem liar_fails_interval_any_cell (p : ℚ) (P : History) (n m : ℕ) {lo hi : ℚ}
    (hlo : 0 ≤ lo) (hhi : hi < 1)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    ¬ ((lo : ℝ) * P n (liarCell T p m lo hi) < P n (liar T p m ⋏ liarCell T p m lo hi) ∧
        P n (liar T p m ⋏ liarCell T p m lo hi) ≤ (hi : ℝ) * P n (liarCell T p m lo hi)) :=
  decided_fails_interval (TheoryWorlds (paperDP T)) (liar T p m) (liarCell T p m lo hi) (P n)
    (liar_decided T p m) hlo hhi hresp hpos

/-- Instance at a straddling cell: threshold `½`, cell `(¼, ¾]` (`lo < p ≤ hi`). -/
theorem liar_fails_interval_straddling (P : History) (n m : ℕ)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T (1 / 2) m)
      (liarCell T (1 / 2) m (1 / 4) (3 / 4)))
    (hpos : 0 < P n (liarCell T (1 / 2) m (1 / 4) (3 / 4))) :
    ¬ (((1 / 4 : ℚ) : ℝ) * P n (liarCell T (1 / 2) m (1 / 4) (3 / 4)) <
          P n (liar T (1 / 2) m ⋏ liarCell T (1 / 2) m (1 / 4) (3 / 4)) ∧
        P n (liar T (1 / 2) m ⋏ liarCell T (1 / 2) m (1 / 4) (3 / 4)) ≤
          ((3 / 4 : ℚ) : ℝ) * P n (liarCell T (1 / 2) m (1 / 4) (3 / 4))) :=
  liar_fails_interval_any_cell T (1 / 2) P n m (by norm_num) (by norm_num) hresp hpos

omit [𝗣𝗔⁻ ⪯ T] in
/-- A world mixture gives a cell strictly around the paper quote its total mass. -/
theorem mixture_cell_mass {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ)
    (hW : ∀ i, (W i).ConsistentWithTheory (paperDP T)) {m : ℕ} {φ : Sentence} {lo hi : ℚ}
    (hlo : lo < paperQuote T m (Encodable.encode φ))
    (hhi : paperQuote T m (Encodable.encode φ) < hi) (n : ℕ) :
    mixtureHistory W w n (quoteAt T m φ lo hi) = ∑ i, w i := by
  unfold mixtureHistory
  refine Finset.sum_congr rfl fun i _ => ?_
  have hh := holds_quoteAt_of_lt_of_lt T hlo hhi (W i) (hW i)
  rw [PCWorld.payout, if_pos hh, mul_one]

/-- Any history that respects the completed theory on the pair and has positive mass on a cell
`(lo, hi] ∈ cells m` with `0 ≤ lo`, `hi < 1` fails the interval predicate — no quote condition
and no one-sidedness. -/
theorem not_exactReflectionInterval_of_liar_cell (P : History) (cells : ℕ → Finset (ℚ × ℚ))
    {n m : ℕ} (hnm : n < m) (p : ℚ) {lo hi : ℚ} (hcell : (lo, hi) ∈ cells m)
    (hlo : 0 ≤ lo) (hhi : hi < 1)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    ¬ ExactReflectionInterval (quoteAt T) cells P := by
  intro h
  have key := h n m hnm (liar T p m) (lo, hi) hcell hpos
  exact liar_fails_interval_any_cell T p P n m hlo hhi hresp hpos key

/-- A positive world mixture fails the interval predicate as soon as some liar's day-`m` quote lies
strictly inside a cell `(lo, hi] ∈ cells m` with `0 ≤ lo`, `hi < 1`. -/
theorem mixture_not_exactReflectionInterval {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ)
    (hW : ∀ i, (W i).ConsistentWithTheory (paperDP T)) (hpos : 0 < ∑ i, w i)
    (cells : ℕ → Finset (ℚ × ℚ)) {n m : ℕ} (hnm : n < m) (p : ℚ) {lo hi : ℚ}
    (hcell : (lo, hi) ∈ cells m) (hlo : 0 ≤ lo) (hhi : hi < 1)
    (hqlo : lo < paperQuote T m (Encodable.encode (liar T p m)))
    (hqhi : paperQuote T m (Encodable.encode (liar T p m)) < hi) :
    ¬ ExactReflectionInterval (quoteAt T) cells (mixtureHistory W w) := by
  have hmass := mixture_cell_mass T W w hW hqlo hqhi n
  have hpos' : 0 < mixtureHistory W w n (liarCell T p m lo hi) := by
    show 0 < mixtureHistory W w n (quoteAt T m (liar T p m) lo hi)
    rw [hmass]; exact hpos
  have hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (mixtureHistory W w n) (liar T p m)
      (liarCell T p m lo hi) :=
    mixture_respectsEntailment (𝒲 := TheoryWorlds (paperDP T)) W w hW _ _
  exact not_exactReflectionInterval_of_liar_cell T _ cells hnm p hcell hlo hhi hresp hpos'

end Cells

section Asymp

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [LO.Entailment.Consistent T]

/-- From `thm:lp` (`lia_liar_asymptotic`): for a cell `0 ≤ lo < hi < 1` and every `n`, some day
`m > n` has the quote of the liar at threshold `(lo + hi)/2` strictly inside the cell. -/
theorem exists_liar_quote_interior {lo hi : ℚ} (hlt : lo < hi) (hlo : 0 ≤ lo) (hhi : hi < 1)
    (n : ℕ) :
    ∃ m, n < m ∧ lo < paperQuote T m (Encodable.encode (liar T ((lo + hi) / 2) m)) ∧
      paperQuote T m (Encodable.encode (liar T ((lo + hi) / 2) m)) < hi := by
  have hp₀ : 0 < (lo + hi) / 2 := by linarith
  have hp₁ : (lo + hi) / 2 < 1 := by linarith
  have h := lia_liar_asymptotic T ((lo + hi) / 2) hp₀ hp₁
  unfold AsympEq at h
  have hε : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
    have : (0 : ℚ) < (hi - lo) / 2 := by linarith
    exact_mod_cast this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h _ hε
  refine ⟨max N (n + 1), lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _), ?_⟩
  have hd := hN (max N (n + 1)) (le_max_left _ _)
  dsimp only at hd
  rw [Real.dist_eq, sub_zero, paperQuote_eq_liaHistory, abs_sub_lt_iff] at hd
  obtain ⟨h1, h2⟩ := hd
  have hpR : ((((lo + hi) / 2 : ℚ)) : ℝ) = ((lo : ℝ) + (hi : ℝ)) / 2 := by push_cast; ring
  have hεR : (((hi - lo) / 2 : ℚ) : ℝ) = ((hi : ℝ) - (lo : ℝ)) / 2 := by push_cast; ring
  rw [hpR, hεR] at h1 h2
  constructor
  · have : (lo : ℝ) <
        ((paperQuote T (max N (n + 1)) (Encodable.encode (liar T ((lo + hi) / 2) (max N (n + 1))))
          : ℚ) : ℝ) := by linarith
    exact_mod_cast this
  · have : ((paperQuote T (max N (n + 1)) (Encodable.encode (liar T ((lo + hi) / 2) (max N (n + 1))))
          : ℚ) : ℝ) < (hi : ℝ) := by linarith
    exact_mod_cast this

/-- **The package's OPEN, answered negatively** for every family with a persistent cell `(lo, hi]`,
`0 ≤ lo < hi < 1` (`x3Cells`; every fixed-resolution dyadic partition of `(0, 1]` at resolution
`≥ 1`): no positive finite mixture of completed-theory worlds satisfies the interval predicate over
every sentence. Only `thm:lp` is used. -/
theorem no_mixture_exactReflectionInterval (cells : ℕ → Finset (ℚ × ℚ)) {lo hi : ℚ}
    (hlt : lo < hi) (hlo : 0 ≤ lo) (hhi : hi < 1) (hcells : ∀ m, (lo, hi) ∈ cells m)
    {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ)
    (hW : ∀ i, (W i).ConsistentWithTheory (paperDP T)) (hpos : 0 < ∑ i, w i) :
    ¬ ExactReflectionInterval (quoteAt T) cells (mixtureHistory W w) := by
  obtain ⟨m, hm, hqlo, hqhi⟩ := exists_liar_quote_interior T hlt hlo hhi 0
  exact mixture_not_exactReflectionInterval T W w hW hpos cells hm _ (hcells m) hlo hhi hqlo hqhi

/-- The point-mass case: no completed-theory point mass inhabits the interval predicate on such a
family (the interval analogue of the package's `pointWorld_not_exactReflection`). -/
theorem no_pointWorld_exactReflectionInterval (cells : ℕ → Finset (ℚ × ℚ)) {lo hi : ℚ}
    (hlt : lo < hi) (hlo : 0 ≤ lo) (hhi : hi < 1) (hcells : ∀ m, (lo, hi) ∈ cells m)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    ¬ ExactReflectionInterval (quoteAt T) cells (pointWorldHistory v) := by
  have heq : pointWorldHistory v = mixtureHistory (fun _ : Fin 1 => v) (fun _ => (1 : ℝ)) := by
    funext n ψ
    simp [pointWorldHistory, mixtureHistory]
  rw [heq]
  exact no_mixture_exactReflectionInterval T cells hlt hlo hhi hcells _ _ (fun _ => hv) (by simp)

/-- At X3's family `{(0, ½], (½, 1]}` (the shape of `Perturb.lean`'s `x3Cells`, restated here so the
probe does not import `Perturb`): no positive world mixture is interval-exact. -/
theorem no_mixture_exactReflectionInterval_x3Cells {k : ℕ} (W : Fin k → PCWorld)
    (w : Fin k → ℝ) (hW : ∀ i, (W i).ConsistentWithTheory (paperDP T)) (hpos : 0 < ∑ i, w i) :
    ¬ ExactReflectionInterval (quoteAt T)
        (fun _ => ({((0 : ℚ), (1 / 2 : ℚ)), ((1 / 2 : ℚ), (1 : ℚ))} : Finset (ℚ × ℚ)))
        (mixtureHistory W w) :=
  no_mixture_exactReflectionInterval T _ (lo := 0) (hi := 1 / 2) (by norm_num) le_rfl
    (by norm_num) (fun _ => by simp) W w hW hpos

end Asymp

end Cleanroom.Bli.BliExactness.AuditR3
