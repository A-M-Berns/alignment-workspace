import Cleanroom.Bli.BliTrajectory.Parser

/-!
# `bli-trajectory` · Marginals: the forward chain probability is the `trajLaw` mass

`bli-finite`'s `trajLaw` is snoc-oriented (the last day split off); `chainProbH` splits off the
first day. This file builds the front decomposition of a trajectory (`Traj.cons`/`first`/
`tail`, a bijection `grid (n+1) × trajGrid (n+1) k ≃ trajGrid n (k+1)`), proves the trajectory
law factors through it (`trajLaw_cons`), and identifies `chainProbH` with the mass `trajLaw`
gives the chain's event (`chainProbH_eq_trajMass`) — the "prove they agree" of the mandate's
D2, closing findings F-15.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

/-! ## Front decomposition of trajectories -/

section Front

variable {𝒮 : SmallIndex} {n : ℕ}

/-- Prepend a first table to a trajectory started one day later.
Source: none: infrastructure (mandate D2, "prove they agree")
Kind: D
Fidelity: n/a -/
def Traj.cons (A : Table 𝒮 (n + 1)) : {k : ℕ} → Traj 𝒮 (n + 1) k → Traj 𝒮 n (k + 1)
  | 0, _ => show Traj 𝒮 n 0 × Table 𝒮 (n + 0 + 1) from (PUnit.unit, A)
  | k + 1, τ' =>
    show Traj 𝒮 n (k + 1) × Table 𝒮 (n + (k + 1) + 1) from
      (Traj.cons A (τ'.1), (τ'.2 : Table 𝒮 (n + 1 + k + 1)).castDay (by omega))

/-- The first table of a nonempty trajectory.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Traj.first : {k : ℕ} → Traj 𝒮 n (k + 1) → Table 𝒮 (n + 1)
  | 0, τ => (τ.2 : Table 𝒮 (n + 0 + 1))
  | k + 1, τ => Traj.first (τ.1 : Traj 𝒮 n (k + 1))

/-- The trajectory after its first table, restarted one day later.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Traj.tail : {k : ℕ} → Traj 𝒮 n (k + 1) → Traj 𝒮 (n + 1) k
  | 0, _ => PUnit.unit
  | k + 1, τ =>
    show Traj 𝒮 (n + 1) k × Table 𝒮 (n + 1 + k + 1) from
      (Traj.tail (τ.1 : Traj 𝒮 n (k + 1)), (τ.2 : Table 𝒮 (n + (k + 1) + 1)).castDay (by omega))

/-- Transport along two equalities of days collapses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Table.castDay_castDay {m m' : ℕ} (h : m = m') (h' : m' = m) (Q : Table 𝒮 m) :
    (Q.castDay h).castDay h' = Q := by subst h; rfl

/-- `first_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.first_cons (A : Table 𝒮 (n + 1)) : ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
    Traj.first (Traj.cons A τ') = A
  | 0, _ => rfl
  | k + 1, τ' => Traj.first_cons A (τ'.1 : Traj 𝒮 (n + 1) k)

/-- `tail_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.tail_cons (A : Table 𝒮 (n + 1)) : ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
    Traj.tail (Traj.cons A τ') = τ'
  | 0, _ => rfl
  | k + 1, τ' => by
    show (Traj.tail (Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k)), _) = τ'
    rw [Traj.tail_cons A]
    rfl

/-- `cons_first_tail`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.cons_first_tail : ∀ {k : ℕ} (τ : Traj 𝒮 n (k + 1)),
    Traj.cons (Traj.first τ) (Traj.tail τ) = τ
  | 0, _ => rfl
  | k + 1, τ => by
    show (Traj.cons (Traj.first τ) (Traj.tail (τ.1 : Traj 𝒮 n (k + 1))), _) = τ
    have ih := Traj.cons_first_tail (τ.1 : Traj 𝒮 n (k + 1))
    show (Traj.cons (Traj.first (τ.1 : Traj 𝒮 n (k + 1))) (Traj.tail (τ.1 : Traj 𝒮 n (k + 1))), _) = τ
    rw [ih]
    rfl

/-- Transport preserves grid membership.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma castDay_mem_grid_iff {d : ℕ → ℕ} {m m' : ℕ} (h : m = m') (Q : Table 𝒮 m) :
    Q.castDay h ∈ grid 𝒮 d m' ↔ Q ∈ grid 𝒮 d m := by subst h; rfl

/-- `cons_mem_trajGrid`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.cons_mem_trajGrid {d : ℕ → ℕ} (A : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
      Traj.cons A τ' ∈ trajGrid 𝒮 d n (k + 1) ↔ A ∈ grid 𝒮 d (n + 1) ∧ τ' ∈ trajGrid 𝒮 d (n + 1) k
  | 0, τ' => by
    show (show Traj 𝒮 n (0 + 1) from (PUnit.unit, A)) ∈ trajGrid 𝒮 d n (0 + 1) ↔ _
    rw [mem_trajGrid_succ]
    exact ⟨fun h => ⟨h.2, mem_trajGrid_zero τ'⟩, fun h => ⟨mem_trajGrid_zero _, h.1⟩⟩
  | k + 1, τ' => by
    show (show Traj 𝒮 n (k + 1 + 1) from (Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k), _)) ∈
        trajGrid 𝒮 d n (k + 1 + 1) ↔
      A ∈ grid 𝒮 d (n + 1) ∧ (show Traj 𝒮 (n + 1) (k + 1) from
        ((τ'.1 : Traj 𝒮 (n + 1) k), (τ'.2 : Table 𝒮 (n + 1 + k + 1)))) ∈
          trajGrid 𝒮 d (n + 1) (k + 1)
    rw [mem_trajGrid_succ, mem_trajGrid_succ, Traj.cons_mem_trajGrid A (τ'.1 : Traj 𝒮 (n + 1) k),
      castDay_mem_grid_iff, and_assoc]

/-- The last table of a prepended trajectory.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.last_cons (t : Table 𝒮 n) (A : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
      (Traj.cons A τ').last t = (τ'.last A).castDay (by omega)
  | 0, _ => rfl
  | k + 1, _ => rfl

/-- **The trajectory law factors through the front decomposition**: the law of `A` followed by
`τ'` is the kernel entry at `A` times the law of `τ'` restarted from `A`.
Source: bli-soto-a-035 (chain rule, first step); mandate D2
Kind: P
Fidelity: exact
Hyps: (a) none -/
lemma trajLaw_cons {d : ℕ → ℕ} (sk : Skeleton 𝒮 d) (t : Table 𝒮 n) (A : Table 𝒮 (n + 1)) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k),
      trajLaw sk n (k + 1) t (Traj.cons A τ') = (sk.κ n).law t A * trajLaw sk (n + 1) k A τ'
  | 0, _ => by
    show trajLaw sk n 0 t PUnit.unit * (sk.κ (n + 0)).law (Traj.last t PUnit.unit) A =
      (sk.κ n).law t A * 1
    rw [trajLaw_zero, Traj.last_zero, one_mul, mul_one]
    rfl
  | k + 1, τ' => by
    show trajLaw sk n (k + 1) t (Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k)) *
        (sk.κ (n + (k + 1))).law ((Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k)).last t)
          ((τ'.2 : Table 𝒮 (n + 1 + k + 1)).castDay (by omega)) =
      (sk.κ n).law t A * (trajLaw sk (n + 1) k A (τ'.1 : Traj 𝒮 (n + 1) k) *
        (sk.κ (n + 1 + k)).law ((τ'.1 : Traj 𝒮 (n + 1) k).last A) (τ'.2 : Table 𝒮 (n + 1 + k + 1)))
    rw [trajLaw_cons sk t A (τ'.1 : Traj 𝒮 (n + 1) k), Traj.last_cons,
      Skeleton.law_castDay sk (by omega : n + 1 + k = n + (k + 1))]
    ring

/-- The day-`(n+1)` table of a prepended trajectory is the prepended table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.day_cons_succ (A : Table 𝒮 (n + 1)) : ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k)
    (h1 : n < n + 1) (h2 : n + 1 ≤ n + (k + 1)), (Traj.cons A τ').day (n + 1) h1 h2 = A
  | 0, _, _, _ => by
    show (if hme : n + 1 = n + 0 + 1 then A.castDay hme.symm else _) = A
    rw [dif_pos rfl]; rfl
  | k + 1, τ', h1, h2 => by
    show (if hme : n + 1 = n + (k + 1) + 1 then _ else
      (Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k)).day (n + 1) h1 (by omega)) = A
    rw [dif_neg (by omega)]
    exact Traj.day_cons_succ A _ h1 _

/-- The later days of a prepended trajectory are those of the tail.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.day_cons_of_gt (A : Table 𝒮 (n + 1)) : ∀ {k : ℕ} (τ' : Traj 𝒮 (n + 1) k) {m : ℕ}
    (hm : n + 1 < m) (h1 : n < m) (h2 : m ≤ n + (k + 1)) (h2' : m ≤ n + 1 + k),
      (Traj.cons A τ').day m h1 h2 = τ'.day m hm h2'
  | 0, _, m, hm, _, h2, _ => absurd h2 (by omega)
  | k + 1, τ', m, hm, h1, h2, h2' => by
    show (if hme : m = n + (k + 1) + 1 then
        ((τ'.2 : Table 𝒮 (n + 1 + k + 1)).castDay (by omega)).castDay hme.symm
      else (Traj.cons A (τ'.1 : Traj 𝒮 (n + 1) k)).day m h1 (by omega)) =
      (if hme' : m = n + 1 + k + 1 then (τ'.2 : Table 𝒮 (n + 1 + k + 1)).castDay hme'.symm
        else (τ'.1 : Traj 𝒮 (n + 1) k).day m hm (by omega))
    by_cases hme : m = n + (k + 1) + 1
    · rw [dif_pos hme, dif_pos (by omega)]
      subst hme; rfl
    · rw [dif_neg hme, dif_neg (by omega)]
      exact Traj.day_cons_of_gt A _ hm h1 _ _

/-- The day-`(n+1)` table of a prepended trajectory, at a day equal to `n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.day_cons_of_eq (A : Table 𝒮 (n + 1)) {k : ℕ} (τ' : Traj 𝒮 (n + 1) k) {m : ℕ}
    (hm : m = n + 1) (h1 : n < m) (h2 : m ≤ n + (k + 1)) :
    (Traj.cons A τ').day m h1 h2 = A.castDay hm.symm := by
  subst hm; exact Traj.day_cons_succ A τ' h1 h2

/-- **Sums over `trajGrid n (k+1)` decompose along the first day.**
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_trajGrid_cons {d : ℕ → ℕ} {k : ℕ} (f : Traj 𝒮 n (k + 1) → ℚ) :
    ∑ τ ∈ trajGrid 𝒮 d n (k + 1), f τ =
      ∑ A ∈ grid 𝒮 d (n + 1), ∑ τ' ∈ trajGrid 𝒮 d (n + 1) k, f (Traj.cons A τ') := by
  have e : ∑ A ∈ grid 𝒮 d (n + 1), ∑ τ' ∈ trajGrid 𝒮 d (n + 1) k, f (Traj.cons A τ') =
      ∑ p ∈ grid 𝒮 d (n + 1) ×ˢ trajGrid 𝒮 d (n + 1) k, f (Traj.cons p.1 p.2) :=
    (Finset.sum_product _ _ (fun p => f (Traj.cons p.1 p.2))).symm
  rw [e]
  refine Finset.sum_nbij' (fun τ => (Traj.first τ, Traj.tail τ)) (fun p => Traj.cons p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [Finset.mem_product]
    have := (Traj.cons_mem_trajGrid (Traj.first τ) (Traj.tail τ)).mp
      (by rw [Traj.cons_first_tail]; exact hτ)
    exact this
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (Traj.cons_mem_trajGrid p.1 p.2).mpr hp
  · intro τ _; exact Traj.cons_first_tail τ
  · intro p _; simp only [Traj.first_cons, Traj.tail_cons]
  · intro τ _; rw [Traj.cons_first_tail]

end Front

/-! ## The identification -/

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (sk : Skeleton smallIndex 𝓜.d)

/-- The event that a trajectory passes through the chain's codes.
Source: mandate D2
Kind: D
Fidelity: n/a -/
noncomputable def ChainEvent (n : ℕ) (l : List (ℕ × ℕ)) {H : ℕ} (τ : Traj smallIndex n H) : Prop :=
  ∀ x ∈ l, ∀ (h1 : n < x.1) (h2 : x.1 ≤ n + H), c.code x.1 (τ.day x.1 h1 h2) = x.2

/-- **The mass `trajLaw` gives the chain's event** — the mandate's D2 price.
Source: mandate D2
Kind: D
Fidelity: exact -/
noncomputable def trajMass (n : ℕ) (t : Table smallIndex n) (l : List (ℕ × ℕ)) (H : ℕ) : ℚ :=
  ∑ τ ∈ trajGrid smallIndex 𝓜.d n H, if ChainEvent c n l τ then trajLaw sk n H t τ else 0

/-- The code of a transported table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma code_castDay {m m' : ℕ} (h : m = m') (A : Table smallIndex m) :
    c.code m' (A.castDay h) = c.code m A := by subst h; rfl

/-- The event on a prepended trajectory: the day-`(n+1)` entries code `A`, and the tail's event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainEvent_cons (n : ℕ) (l : List (ℕ × ℕ)) {H : ℕ} (A : Table smallIndex (n + 1))
    (τ' : Traj smallIndex (n + 1) H) :
    ChainEvent c n l (Traj.cons A τ') ↔
      (∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) A = x.2) ∧ ChainEvent c (n + 1) l τ' := by
  constructor
  · intro h
    refine ⟨fun x hx hx1 => ?_, fun x hx h1 h2 => ?_⟩
    · have := h x hx (by omega) (by omega)
      rwa [Traj.day_cons_of_eq A τ' hx1, code_castDay] at this
    · have := h x hx (by omega) (by omega)
      rwa [Traj.day_cons_of_gt A τ' h1 _ _ h2] at this
  · rintro ⟨hA, hτ⟩ x hx h1 h2
    by_cases hx1 : x.1 = n + 1
    · rw [Traj.day_cons_of_eq A τ' hx1, code_castDay]
      exact hA x hx hx1
    · rw [Traj.day_cons_of_gt A τ' (by omega) h1 h2 (by omega)]
      exact hτ x hx (by omega) (by omega)

/-- **`chainProbH_eq_trajMass` — the forward chain probability is the `trajLaw` mass of the
chain's event** (the mandate's "prove they agree"): induction on the horizon through the front
decomposition, `trajLaw_cons` and `chainEvent_cons`.
Source: mandate D2; [[bli-program]] §2.5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem chainProbH_eq_trajMass (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n), chainProbH sk c l n t H = trajMass c sk n t l H
  | 0, n, t => by
    unfold trajMass
    rw [sum_trajGrid_zero]
    split_ifs with hev
    · rfl
    · exact absurd (fun x _ h1 h2 => absurd h2 (by omega)) hev
  | H + 1, n, t => by
    unfold trajMass
    rw [sum_trajGrid_cons, chainProbH_succ]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [chainProbH_eq_trajMass l H (n + 1) A]
    unfold trajMass
    by_cases hA : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) A = x.2
    · rw [if_pos hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      rw [trajLaw_cons]
      by_cases hτ : ChainEvent c (n + 1) l τ'
      · rw [if_pos ((chainEvent_cons c n l A τ').mpr ⟨hA, hτ⟩), if_pos hτ]
      · rw [if_neg (fun h => hτ ((chainEvent_cons c n l A τ').mp h).2), if_neg hτ, mul_zero]
    · rw [if_neg hA, mul_zero]
      refine (Finset.sum_eq_zero fun τ' _ => ?_).symm
      rw [if_neg (fun h => hA ((chainEvent_cons c n l A τ').mp h).1)]

end Cleanroom.Bli.BliTrajectory
