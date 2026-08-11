/-
  Kernel-checkable formalization tying the NEGATIVE result
  (`anson-notes/no-timely-pointwise-tower.md`) to the POSITIVE result
  (`faithful-acceleration.md`), following the synthesis explainer
  `pointwise-tower-and-faithful-acceleration.md`.

  Two pieces, both genuinely NEW relative to the existing four modules.

  ── PART 1 ── the reduction that makes the negative result about the TOWER.
    `SelfReferentialTarget.lean` proves *tracking* fails (`tracking_fails`, 2a) but starts FROM
    tracking.  The distinctive content of `no-timely-pointwise-tower.md` §2 is that the timely
    pointwise *tower* `Mart(H→A)` REDUCES to tracking, via two corner-quote collapses —
    read-off (`E^H_n⌜aₙ⌝ ≈ₙ aₙ`, decided-sentence convergence) and self-trust `cee`
    (`E^H_n X ≈ₙ E^H_n⌜Yₙ⌝`) — plus present-accuracy on the diagonal (`E^H_n⌜Yₙ⌝ ≈ₙ Yₙ`).
    `tower_imp_tracking` is that reduction (pure `≈ₙ` algebra); `pointwise_tower_fails`
    composes it with tracking-failure — taken as a NAMED input, since it is exactly
    `SelfReferentialTarget.tracking_fails` and the modules are standalone, as throughout this
    development — to refute the tower itself.  This is what makes the negative result about
    *the same object* (the tower) that the positive result is about.

  ── PART 2 ── the two faces are genuinely distinct (the integration's non-vacuity).
    The explainer's load-bearing reconciliation: a single bounded sequence can be
    PERSISTENTLY WRONG per index — pointwise `|aₙ − Yₙ| = ½`, so tracking/the tower is dead
    (the negative face) — yet UNBIASED IN AGGREGATE — the weighted bias stays bounded while the
    weight diverges, i.e. the average bias → 0 (gated Total Trust, the positive face).
    `two_faces_distinct` exhibits it; the witness is A's best-response quote `aₙ ≡ ½` against an
    alternating realized credence `Yₙ ∈ {0,1}`: the exact ½-defect of 2a, averaged away.
    `tower_dead_on_witness` runs that witness through Part 1 — the SAME sequence that satisfies
    averaged trust has a dead pointwise tower.

  Discipline (identical to the other modules): genuine arithmetic/asymptotic content PROVED;
  the one LI/sibling fact (tracking-failure) enters only as a named hypothesis.  No `sorry`;
  axiom audit at the end (each result on `[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib

open Filter Topology

namespace TowerAccel

/-! ## Asymptotic calculus (`Approx a b` is LI's `a ≈ₙ b`; mirrors `SelfRefTarget`). -/

def Approx (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)

theorem approx_refl (a : ℕ → ℝ) : Approx a a := by
  unfold Approx
  have heq : (fun n => a n - a n) = (fun _ => (0 : ℝ)) := by funext n; ring
  rw [heq]; exact tendsto_const_nhds

theorem approx_symm {a b : ℕ → ℝ} (h : Approx a b) : Approx b a := by
  unfold Approx at h ⊢
  have h2 := h.neg
  rw [neg_zero] at h2
  have heq : (fun n => -(a n - b n)) = (fun n => b n - a n) := by funext n; ring
  rw [heq] at h2; exact h2

theorem approx_trans {a b c : ℕ → ℝ} (h1 : Approx a b) (h2 : Approx b c) : Approx a c := by
  unfold Approx at h1 h2 ⊢
  have h3 := h1.add h2
  rw [add_zero] at h3
  have heq : (fun n => (a n - b n) + (b n - c n)) = (fun n => a n - c n) := by funext n; ring
  rw [heq] at h3; exact h3

/- ====================================================================================
   PART 1 — the timely pointwise tower reduces to tracking  (no-timely §2).
   ==================================================================================== -/

/-- **The reduction (the new content).**  The tower instance `Approx EhX Eha`, with its two
    corner-quote collapses — `hRead : Approx Eha a` (read-off of A's decided quote),
    `hCee : Approx EhX EhY` (self-trust `cee`), `hAcc : Approx EhY Y` (present-accuracy on the
    diagonal) — yields timely pointwise tracking `Approx a Y`.  Pure `≈ₙ` algebra:
    `a ≈ Eha ≈ EhX ≈ EhY ≈ Y`. -/
theorem tower_imp_tracking {EhX Eha EhY a Y : ℕ → ℝ}
    (hTower : Approx EhX Eha) (hRead : Approx Eha a)
    (hCee : Approx EhX EhY) (hAcc : Approx EhY Y) :
    Approx a Y :=
  approx_trans (approx_trans (approx_trans (approx_symm hRead) (approx_symm hTower)) hCee) hAcc

/-- **The timely pointwise tower is false** wherever tracking is.  `hTrackingFails` is exactly
    `SelfReferentialTarget.tracking_fails` (the 2a anti-inductive-diagonal result), reused here
    as a named input.  Composing it with the reduction lifts the 2a impossibility from
    *tracking* up to the *tower* `Mart(H→A)` itself. -/
theorem pointwise_tower_fails {EhX Eha EhY a Y : ℕ → ℝ}
    (hRead : Approx Eha a) (hCee : Approx EhX EhY) (hAcc : Approx EhY Y)
    (hTrackingFails : ¬ Approx a Y) :
    ¬ Approx EhX Eha :=
  fun hTower => hTrackingFails (tower_imp_tracking hTower hRead hCee hAcc)

/- ====================================================================================
   PART 2 — the two faces are genuinely distinct  (integration non-vacuity).
   Witness: A's best-response quote `aₙ ≡ ½` vs. an alternating realized credence
   `Yₙ = ½ − ½(−1)ⁿ ∈ {0,1}`.  Pointwise defect ≡ ½ (tower dead); aggregate bias bounded
   while the weight diverges (averaged Total Trust holds).
   ==================================================================================== -/

/-- A's forecast: the best-response quote, constant `½` (cf. `SelfRefTarget.residual_half`). -/
noncomputable def wa (n : ℕ) : ℝ := 1 / 2
/-- The realized future credence: `½ − ½(−1)ⁿ`, i.e. the alternating flip `0,1,0,1,…`. -/
noncomputable def wY (n : ℕ) : ℝ := 1 / 2 - 1 / 2 * (-1) ^ n
/-- Uniform weight. -/
noncomputable def ww (n : ℕ) : ℝ := 1

/-- Closed form of the bias partial sum: `∑_{i<n}(Yᵢ − aᵢ) = ((−1)ⁿ − 1)/4`, valued in
    `[−½, 0]` — bounded, though the summands never vanish. -/
theorem witness_partial_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (wY i - wa i)) = ((-1 : ℝ) ^ n - 1) / 4 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [wY, wa, pow_succ]
    ring

/-- The pointwise defect is exactly `½` at every index (the 2a tight bound). -/
theorem witness_gap (n : ℕ) : |wa n - wY n| = 1 / 2 := by
  have he : wa n - wY n = 1 / 2 * (-1) ^ n := by simp only [wa, wY]; ring
  have habs : |(-1 : ℝ) ^ n| = 1 := by simp [abs_pow]
  rw [he, abs_mul, habs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num

/-- Pointwise tracking fails on the witness by a constant `½` — so the tower is dead here. -/
theorem witness_tracking_fails : ¬ Approx wa wY := by
  intro hA
  have h2 : Tendsto (fun n => |wa n - wY n|) atTop (𝓝 0) := by
    unfold Approx at hA; simpa using hA.abs
  have hconst : (fun n => |wa n - wY n|) = (fun _ => (1 / 2 : ℝ)) := by
    funext n; exact witness_gap n
  rw [hconst] at h2
  have huniq := tendsto_nhds_unique h2 tendsto_const_nhds
  norm_num at huniq

/-- **The two faces of deference are genuinely distinct** — the integration's load-bearing
    fact.  A single bounded sequence (A's best-response quote `aₙ ≡ ½` against the alternating
    realized credence `Yₙ ∈ {0,1}`) is at once:
      • (NEGATIVE) persistently wrong per index — `½ ≤ |aₙ − Yₙ|`, hence `¬ Approx a Y`: the
        timely pointwise tower is dead (Part 1);
      • (POSITIVE) unbiased in aggregate — the weighted bias `∑ wᵢ(Yᵢ − aᵢ)` stays bounded
        (`≤ ½`) while the weight `∑ wᵢ → ∞`, so the average bias → 0: gated Total Trust holds.
    Wrong-per-index, unbiased-in-aggregate: the exact `½`-defect that kills the pointwise tower
    (2a), averaged away — and so the negative and positive results never collide. -/
theorem two_faces_distinct :
    ∃ a Y w : ℕ → ℝ,
      (∀ n, 0 ≤ a n ∧ a n ≤ 1) ∧
      (∀ n, 0 ≤ Y n ∧ Y n ≤ 1) ∧
      (∀ n, 1 / 2 ≤ |a n - Y n|) ∧
      ¬ Approx a Y ∧
      (∀ n, |∑ i ∈ Finset.range n, w i * (Y i - a i)| ≤ 1 / 2) ∧
      Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop := by
  refine ⟨wa, wY, ww, ?_, ?_, ?_, witness_tracking_fails, ?_, ?_⟩
  · -- a ∈ [0,1]
    intro n; refine ⟨?_, ?_⟩
    · simp only [wa]; norm_num
    · simp only [wa]; norm_num
  · -- Y ∈ [0,1]
    intro n
    have habs : |(-1 : ℝ) ^ n| = 1 := by simp [abs_pow]
    have hb := abs_le.mp (le_of_eq habs)
    refine ⟨?_, ?_⟩
    · simp only [wY]; linarith [hb.1, hb.2]
    · simp only [wY]; linarith [hb.1, hb.2]
  · -- pointwise defect ≥ ½
    intro n; exact le_of_eq (witness_gap n).symm
  · -- aggregate bias bounded by ½
    intro n
    simp only [ww, one_mul]
    rw [witness_partial_sum n]
    have habs : |(-1 : ℝ) ^ n| = 1 := by simp [abs_pow]
    have hb := abs_le.mp (le_of_eq habs)
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  · -- weight diverges
    have hWconst : (fun n => ∑ i ∈ Finset.range n, ww i) = (fun n : ℕ => (n : ℝ)) := by
      funext n
      simp only [ww, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hWconst]; exact tendsto_natCast_atTop_atTop

/-- **Capstone — the synthesis in one statement.**  The very witness that satisfies averaged
    trust (`two_faces_distinct`) has a DEAD pointwise tower: feeding its tracking-failure
    through the Part-1 reduction (the corner-quote collapses are trivial here) refutes the
    tower instance `Approx wY wa`. -/
theorem tower_dead_on_witness : ¬ Approx wY wa :=
  pointwise_tower_fails (approx_refl wa) (approx_refl wY) (approx_refl wY) witness_tracking_fails

end TowerAccel

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms TowerAccel.approx_refl
#print axioms TowerAccel.approx_symm
#print axioms TowerAccel.approx_trans
#print axioms TowerAccel.tower_imp_tracking
#print axioms TowerAccel.pointwise_tower_fails
#print axioms TowerAccel.witness_partial_sum
#print axioms TowerAccel.witness_gap
#print axioms TowerAccel.witness_tracking_fails
#print axioms TowerAccel.two_faces_distinct
#print axioms TowerAccel.tower_dead_on_witness
