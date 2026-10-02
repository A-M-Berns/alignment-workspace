import Cleanroom.Bli.BliMeasure.Grid
import Cleanroom.Bli.BliFinite.Kernel

/-!
# `bli-measure` · Kernel: carrier-indexed kernels and the trajectory law over the coherent grid
(target 0)

`bli-finite`'s `Kernel`/`Skeleton` are hard-wired to the product grid (`IsProb d`), so they are
**generalized, not bent** (mandate Known issue 12): `KernelOn 𝒮 G m` is a kernel whose laws are
probabilities on an arbitrary day-indexed carrier `G (m+1)` and balanced on `G m`, with the
off-carrier law pinned to `0` (junk, disclosed, never charged). `ctrajGrid`/`ctrajLaw` are
`trajGrid`/`trajLaw` over such a skeleton, with the four lemmas re-proved (`ctrajLaw_nonneg`,
`_support`, `_marginal`, `_sum_one`) and two more this package needs:

* **the front decomposition** `Traj.cons` / `ctrajLaw_cons` / `sum_ctrajGrid_cons` — a
  horizon-`(k+1)` trajectory from day `n` is a first table and a horizon-`k` trajectory from day
  `n+1`, and the law factors accordingly (the restart identity `TB` runs on);
* **pinning along the chain** `ctraj_zero_persists` — a coordinate at `0` in the start table stays
  `0` on every charged trajectory (`IsProbOn.coord_eq_zero_of_meanOn_eq_zero` day by day), which
  is what keeps the stage-free kernel inside the support of the base's measure (target 1(b)).
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex}

/-! ## Kernels on a carrier -/

/-- **One-step kernel on a day-indexed carrier `G`**: to every day-`m` table a superbelief that is
a probability on `G (m+1)` and balanced (restricted mean = the table) for tables in `G m`, and
`0` off `G m` (junk, disclosed). Generalizes `bli-finite`'s `Kernel` (product grid) to the
coherent grid.
Source: [[bli-measure-mandate]] target 0 (`KernelOn`); bli-slides-017 constraints 4–5
Kind: D
Fidelity: variant: carrier a parameter; off-carrier law `0` (disclosed) -/
structure KernelOn (𝒮 : SmallIndex) (G : ∀ m, Finset (Table 𝒮 m)) (m : ℕ) where
  /-- The superbelief about day `m+1` given the day-`m` table. -/
  law : Table 𝒮 m → Superbelief 𝒮 (m + 1)
  /-- Each law at a carrier table is a probability on the next carrier. -/
  prob : ∀ t ∈ G m, IsProbOn (G (m + 1)) (law t)
  /-- Balance on the carrier. -/
  balanced : ∀ t ∈ G m, (meanOn (G (m + 1)) (law t)).restrict = t
  /-- Off the carrier the law is zero. -/
  junk : ∀ t ∉ G m, law t = 0

/-- **A skeleton on a carrier**: one kernel per day.
Source: [[bli-measure-mandate]] target 0 (`CoherentSkeleton`)
Kind: D
Fidelity: exact -/
structure SkeletonOn (𝒮 : SmallIndex) (G : ∀ m, Finset (Table 𝒮 m)) where
  /-- The day-`m` kernel. -/
  κ : ∀ m, KernelOn 𝒮 G m

variable {G : ∀ m, Finset (Table 𝒮 m)}

/-- A law is nonnegative everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma KernelOn.law_nonneg {m : ℕ} (κ : KernelOn 𝒮 G m) (t : Table 𝒮 m) (Q : Table 𝒮 (m + 1)) :
    0 ≤ κ.law t Q := by
  by_cases ht : t ∈ G m
  · exact (κ.prob t ht).1 Q
  · rw [κ.junk t ht]; exact le_rfl

/-- A law vanishes off the next carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma KernelOn.law_eq_zero_of_not_mem {m : ℕ} (κ : KernelOn 𝒮 G m) (t : Table 𝒮 m)
    {Q : Table 𝒮 (m + 1)} (hQ : Q ∉ G (m + 1)) : κ.law t Q = 0 := by
  by_cases ht : t ∈ G m
  · exact (κ.prob t ht).2.1 Q hQ
  · rw [κ.junk t ht]; rfl

/-- A charged table is on the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma KernelOn.mem_of_pos {m : ℕ} (κ : KernelOn 𝒮 G m) {t : Table 𝒮 m} {Q : Table 𝒮 (m + 1)}
    (h : 0 < κ.law t Q) : Q ∈ G (m + 1) := by
  by_contra hQ
  rw [κ.law_eq_zero_of_not_mem t hQ] at h
  exact lt_irrefl _ h

/-- The law at a carrier table has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma KernelOn.sum_law {m : ℕ} (κ : KernelOn 𝒮 G m) {t : Table 𝒮 m} (ht : t ∈ G m) :
    ∑ Q ∈ G (m + 1), κ.law t Q = 1 :=
  (κ.prob t ht).2.2

/-- Balance, coordinatewise: the mean at a day-`m` coordinate is the table's value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma KernelOn.sum_law_mul {m : ℕ} (κ : KernelOn 𝒮 G m) {t : Table 𝒮 m} (ht : t ∈ G m)
    (φ : ↥(𝒮.S m)) :
    ∑ Q ∈ G (m + 1), κ.law t Q * Q ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := by
  have := congrFun (κ.balanced t ht) φ
  rw [Table.restrict_apply] at this
  exact this

/-- Transporting both arguments of a law along an equality of days changes nothing.
Source: none: infrastructure (`bli-finite` `Skeleton.law_castDay`)
Kind: L
Fidelity: n/a -/
lemma SkeletonOn.law_castDay (sk : SkeletonOn 𝒮 G) {e e' : ℕ} (he : e = e') (s : Table 𝒮 e)
    (Q : Table 𝒮 (e + 1)) :
    (sk.κ e').law (s.castDay he) (Q.castDay (by rw [he])) = (sk.κ e).law s Q := by
  subst he; rfl

/-- Composition of transports.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma castDay_castDay {m₁ m₂ m₃ : ℕ} (h₁ : m₁ = m₂) (h₂ : m₂ = m₃) (t : Table 𝒮 m₁) :
    (t.castDay h₁).castDay h₂ = t.castDay (h₁.trans h₂) := by
  subst h₁; subst h₂; rfl

/-- A sum over a carrier day can be re-indexed along an equality of days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_castDay (G : ∀ m, Finset (Table 𝒮 m)) {e e' : ℕ} (he : e = e') (g : Table 𝒮 e' → ℚ) :
    ∑ Q ∈ G e', g Q = ∑ Q ∈ G e, g (Q.castDay he) := by
  subst he; rfl

/-! ## The trajectory law over a carrier -/

/-- The finite carrier of day-`n` horizon-`h` trajectories over `G`.
Source: `bli-finite` `trajGrid`, over a carrier
Kind: D
Fidelity: n/a -/
def ctrajGrid (G : ∀ m, Finset (Table 𝒮 m)) (n : ℕ) : (h : ℕ) → Finset (Traj 𝒮 n h)
  | 0 => {PUnit.unit}
  | h + 1 => ctrajGrid G n h ×ˢ G (n + h + 1)

/-- **The trajectory law over a carrier skeleton**, by the Markov recursion.
Source: `bli-finite` `trajLaw`, over a carrier; bli-soto-a-035
Kind: D
Fidelity: exact -/
def ctrajLaw (sk : SkeletonOn 𝒮 G) (n : ℕ) : (h : ℕ) → Table 𝒮 n → Traj 𝒮 n h → ℚ
  | 0, _, _ => 1
  | h + 1, t, (τ, Q) => ctrajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q

variable (sk : SkeletonOn 𝒮 G) {n : ℕ}

/-- Unfolding at horizon `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ctrajLaw_zero (t : Table 𝒮 n) (τ : Traj 𝒮 n 0) : ctrajLaw sk n 0 t τ = 1 := rfl

/-- Unfolding at a successor horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ctrajLaw_succ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h) (Q : Table 𝒮 (n + h + 1)) :
    ctrajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) =
      ctrajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q := rfl

/-- The empty trajectory is on the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ctrajGrid_zero (τ : Traj 𝒮 n 0) : τ ∈ ctrajGrid G n 0 := by
  show τ ∈ ({PUnit.unit} : Finset PUnit)
  exact Finset.mem_singleton.mpr rfl

/-- Membership at a successor horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ctrajGrid_succ {h : ℕ} {τ : Traj 𝒮 n h} {Q : Table 𝒮 (n + h + 1)} :
    (show Traj 𝒮 n (h + 1) from (τ, Q)) ∈ ctrajGrid G n (h + 1) ↔
      τ ∈ ctrajGrid G n h ∧ Q ∈ G (n + h + 1) :=
  Finset.mem_product

/-- Sums at horizon `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_ctrajGrid_zero (f : Traj 𝒮 n 0 → ℚ) : ∑ τ ∈ ctrajGrid G n 0, f τ = f PUnit.unit := by
  show ∑ τ ∈ ({PUnit.unit} : Finset PUnit), f τ = f PUnit.unit
  exact Finset.sum_singleton _ _

/-- Sums at a successor horizon split into the prefix and the last table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_ctrajGrid_succ {h : ℕ} (f : Traj 𝒮 n (h + 1) → ℚ) :
    ∑ τ ∈ ctrajGrid G n (h + 1), f τ =
      ∑ τ ∈ ctrajGrid G n h, ∑ Q ∈ G (n + h + 1), f (show Traj 𝒮 n (h + 1) from (τ, Q)) :=
  Finset.sum_product _ _ _

/-- The last table of a carrier trajectory started on the carrier is on the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.last_mem {t : Table 𝒮 n} (ht : t ∈ G n) :
    ∀ {h : ℕ} {τ : Traj 𝒮 n h}, τ ∈ ctrajGrid G n h → τ.last t ∈ G (n + h)
  | 0, _, _ => ht
  | _ + 1, (_, _), hτ => (mem_ctrajGrid_succ.mp hτ).2

/-- The trajectory law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ctrajLaw_nonneg : ∀ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h), 0 ≤ ctrajLaw sk n h t τ
  | 0, _, _ => by simp
  | h + 1, t, (τ, Q) => by
      rw [ctrajLaw_succ]
      exact mul_nonneg (ctrajLaw_nonneg t τ) ((sk.κ (n + h)).law_nonneg _ _)

/-- The trajectory law vanishes off the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ctrajLaw_support :
    ∀ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h), τ ∉ ctrajGrid G n h → ctrajLaw sk n h t τ = 0
  | 0, _, τ, hτ => absurd (mem_ctrajGrid_zero τ) hτ
  | h + 1, t, (τ, Q), hτ => by
      have hτ' := mt mem_ctrajGrid_succ.mpr hτ
      rw [not_and_or] at hτ'
      rw [ctrajLaw_succ]
      rcases hτ' with hτ | hQ
      · rw [ctrajLaw_support t τ hτ, zero_mul]
      · rw [(sk.κ (n + h)).law_eq_zero_of_not_mem _ hQ, mul_zero]

/-- **Marginalizing the last day** (for a start table on the carrier).
Source: `bli-finite` `trajLaw_marginal`; bli-soto-a-035
Kind: L
Fidelity: exact -/
lemma ctrajLaw_marginal {t : Table 𝒮 n} (ht : t ∈ G n) {h : ℕ} (τ : Traj 𝒮 n h) :
    ∑ Q ∈ G (n + h + 1), ctrajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) =
      ctrajLaw sk n h t τ := by
  by_cases hτ : τ ∈ ctrajGrid G n h
  · simp only [ctrajLaw_succ]
    rw [← Finset.mul_sum, (sk.κ (n + h)).sum_law (Traj.last_mem ht hτ), mul_one]
  · simp [ctrajLaw_succ, ctrajLaw_support sk t τ hτ]

/-- **The trajectory law is a probability** on the carrier trajectories (start on the carrier).
Source: `bli-finite` `trajLaw_sum_one`
Kind: L
Fidelity: exact -/
lemma ctrajLaw_sum_one {t : Table 𝒮 n} (ht : t ∈ G n) :
    ∀ {h : ℕ}, ∑ τ ∈ ctrajGrid G n h, ctrajLaw sk n h t τ = 1
  | 0 => by rw [sum_ctrajGrid_zero]; rfl
  | h + 1 => by
      rw [sum_ctrajGrid_succ]
      simp only [ctrajLaw_marginal sk ht]
      exact ctrajLaw_sum_one ht

/-- `IsProbOn` packaging.
Source: `bli-finite` `trajLaw_isProbOn`
Kind: L
Fidelity: exact -/
lemma ctrajLaw_isProbOn {t : Table 𝒮 n} (ht : t ∈ G n) {h : ℕ} :
    IsProbOn (ctrajGrid G n h) (ctrajLaw sk n h t) :=
  ⟨ctrajLaw_nonneg sk t, fun τ hτ => ctrajLaw_support sk t τ hτ, ctrajLaw_sum_one sk ht⟩

/-! ## The front decomposition -/

/-- **Front-cons**: a first table and a horizon-`k` trajectory from day `n+1` give a horizon-`(k+1)`
trajectory from day `n` (the last table is transported along `n + 1 + k = n + (k + 1)`).
Source: none: infrastructure (mandate target 3, the restart identity)
Kind: D
Fidelity: n/a -/
def Traj.cons (Q : Table 𝒮 (n + 1)) : {k : ℕ} → Traj 𝒮 (n + 1) k → Traj 𝒮 n (k + 1)
  | 0, _ => show Traj 𝒮 n 0 × Table 𝒮 (n + 0 + 1) from (PUnit.unit, Q)
  | k + 1, (τ', Q') =>
      show Traj 𝒮 n (k + 1) × Table 𝒮 (n + (k + 1) + 1) from
        (Traj.cons Q τ', Q'.castDay (by omega))

/-- The last table of a front-cons is the last table of the tail (transported).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.last_cons (t : Table 𝒮 n) (Q : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
      (Traj.cons Q τ').last t = (τ'.last Q).castDay (by omega : n + 1 + k = n + (k + 1))
  | 0, _ => rfl
  | _ + 1, (_, _) => rfl

/-- The day-`(n+1)` table of a front-cons is its first table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.day_cons_first (Q : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k) (hm : n < n + 1) (hmh : n + 1 ≤ n + (k + 1)),
      (Traj.cons Q τ').day (n + 1) hm hmh = Q
  | 0, _, hm, hmh => @Traj.day_last 𝒮 n 0 PUnit.unit Q hm hmh
  | k + 1, (τ', Q'), hm, hmh => by
      show (show Traj 𝒮 n (k + 1 + 1) from (Traj.cons Q τ', Q'.castDay (by omega))).day
        (n + 1) hm hmh = Q
      rw [Traj.day_of_ne _ _ hm hmh (by omega)]
      exact Traj.day_cons_first Q τ' hm (by omega)

/-- The day-`m` table of a front-cons, for `m > n+1`, is the tail's day-`m` table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.day_cons_later (Q : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k) {m : ℕ} (hm : n + 1 < m) (hmh : m ≤ n + 1 + k),
      (Traj.cons Q τ').day m (by omega) (by omega) = τ'.day m hm hmh
  | 0, _, _, hm, hmh => absurd hmh (by omega)
  | k + 1, (τ', Q'), m, hm, hmh => by
      show (show Traj 𝒮 n (k + 1 + 1) from (Traj.cons Q τ', Q'.castDay (by omega))).day
        m (by omega) (by omega) = _
      by_cases hme : m = n + 1 + k + 1
      · subst hme
        rw [Traj.day_last]
        simp only [Traj.day]
        rw [dif_pos (by omega)]
        rw [castDay_castDay]
        exact Table.castDay_rfl Q'
      · rw [Traj.day_of_ne _ _ (by omega) (by omega) (by omega), Traj.day_of_ne _ _ hm hmh hme]
        exact Traj.day_cons_later Q τ' hm (by omega)

/-- **The restart identity**: the law of a front-cons is the first step times the law of the tail
restarted from the first table.
Source: bli-soto-a-035 (chain rule); `bli-assemble` `chainProbH_restart`; mandate target 3
Kind: P
Fidelity: exact
Hyps: (a) none -/
lemma ctrajLaw_cons (t : Table 𝒮 n) (Q : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
      ctrajLaw sk n (k + 1) t (Traj.cons Q τ') = (sk.κ n).law t Q * ctrajLaw sk (n + 1) k Q τ'
  | 0, _ => by
      show ctrajLaw sk n 0 t PUnit.unit * (sk.κ (n + 0)).law (Traj.last t PUnit.unit) Q =
        (sk.κ n).law t Q * 1
      rw [ctrajLaw_zero, one_mul, mul_one]
      rfl
  | k + 1, (τ', Q') => by
      show ctrajLaw sk n (k + 1) t (Traj.cons Q τ') *
          (sk.κ (n + (k + 1))).law ((Traj.cons Q τ').last t) (Q'.castDay (by omega)) =
        (sk.κ n).law t Q * (ctrajLaw sk (n + 1) k Q τ' * (sk.κ (n + 1 + k)).law (τ'.last Q) Q')
      rw [ctrajLaw_cons t Q τ', Traj.last_cons, mul_assoc]
      congr 2
      exact sk.law_castDay (by omega) _ _

/-- **Sums over horizon-`(k+1)` carrier trajectories decompose at the front.**
Source: none: infrastructure (mandate target 3)
Kind: L
Fidelity: n/a -/
lemma sum_ctrajGrid_cons (n : ℕ) : ∀ (k : ℕ) (f : Traj 𝒮 n (k + 1) → ℚ),
    ∑ τ ∈ ctrajGrid G n (k + 1), f τ =
      ∑ Q ∈ G (n + 1), ∑ τ' ∈ ctrajGrid G (n + 1) k, f (Traj.cons Q τ')
  | 0, f => by
      rw [sum_ctrajGrid_succ, sum_ctrajGrid_zero]
      apply Finset.sum_congr rfl
      intro Q _
      rw [sum_ctrajGrid_zero]
      rfl
  | k + 1, f => by
      rw [sum_ctrajGrid_succ, sum_ctrajGrid_cons n k]
      apply Finset.sum_congr rfl
      intro Q _
      rw [sum_ctrajGrid_succ]
      apply Finset.sum_congr rfl
      intro τ' _
      rw [sum_castDay G (by omega : n + 1 + k + 1 = n + (k + 1) + 1)]
      rfl

/-! ## Pinning along the chain -/

/-- **A zero coordinate of the start table stays zero along every charged trajectory** (pinning
at `0`, day by day, on a carrier of unit-cube tables).
Source: bli-slides-021 (pinning); mandate target 1(b) (design note, "along the chain no charged
world refutes it")
Kind: P
Fidelity: exact
Hyps: (a) `hG` (carrier in the unit cube), `ht` -/
theorem ctraj_zero_persists (hG : ∀ m, ∀ Q ∈ G m, Q.InUnit) {t : Table 𝒮 n} (ht : t ∈ G n)
    (φ₀ : ↥(𝒮.S n)) (h0 : t φ₀ = 0) :
    ∀ {h : ℕ} (τ : Traj 𝒮 n h), τ ∈ ctrajGrid G n h → 0 < ctrajLaw sk n h t τ →
      (τ.last t) ⟨φ₀.1, 𝒮.mono_le (Nat.le_add_right n h) φ₀.2⟩ = 0
  | 0, _, _, _ => h0
  | h + 1, (τ, Q), hτ, hpos => by
      rw [mem_ctrajGrid_succ] at hτ
      rw [ctrajLaw_succ] at hpos
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨hτpos, hQpos⟩ | ⟨hneg, -⟩
      · have ih := ctraj_zero_persists hG ht φ₀ h0 τ hτ.1 hτpos
        have hlast : τ.last t ∈ G (n + h) := Traj.last_mem ht hτ.1
        have hmean : meanOn (G (n + h + 1)) ((sk.κ (n + h)).law (τ.last t))
            ⟨φ₀.1, 𝒮.mono_le (Nat.le_add_right n (h + 1)) φ₀.2⟩ = 0 := by
          have := (sk.κ (n + h)).sum_law_mul hlast
            ⟨φ₀.1, 𝒮.mono_le (Nat.le_add_right n h) φ₀.2⟩
          rw [ih] at this
          exact this
        exact IsProbOn.coord_eq_zero_of_meanOn_eq_zero ((sk.κ (n + h)).prob _ hlast)
          (hG _) hmean hQpos
      · exact absurd hneg (not_lt.mpr (ctrajLaw_nonneg sk t τ))

end Cleanroom.Bli.BliMeasure
