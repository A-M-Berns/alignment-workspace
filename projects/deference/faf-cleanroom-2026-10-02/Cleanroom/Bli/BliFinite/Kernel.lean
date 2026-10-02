import Cleanroom.Bli.BliFinite.Superbelief

/-!
# `bli-finite` · Kernel: kernels, skeletons, trajectories, the trajectory law (T6)

Soto's chain rule (bli-soto-a-035): beliefs about day `n+2` are the Markov composition of
one-step beliefs. The program of record reads Appendix B's constraints 2–4 as one object — a
**Markov skeleton** of one-step kernels on the nested grid — whose trajectory law *is* `𝐏`'s
restriction to the state algebra.

Design decisions (mandate 5 and 7): kernels go `m → m+1` (never `m − 1 → m` with `Nat`
subtraction); `Kernel` has **no computability field** (deviation from [[bli-program]] §2.4:
`Computable law` would need a `Primcodable` instance on a function type over a `Finset`
subtype; a reindexed predicate is the stretch target T10); trajectories are dependent tuples
and the law is **defined by the recursion**, with the chain rule **proved** — never the other
way round (the "E3 by listing" squeeze is `bli-trajectory`'s risk, whose root is here).

The trajectory type is *snoc*-oriented (`Traj 𝒮 n (h+1) = Traj 𝒮 n h × Table 𝒮 (n+h+1)`) so
that the last table, the law, the finite carrier and the marginal lemma are cast-free; only
`Traj.append` needs the day identification `n + h + k = n + (h + k)`, done through the
cast-free `Table.castDay`.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction Finset

variable {𝒮 : SmallIndex}

/-! ## Kernels and skeletons -/

/-- **One-step kernel** on day `m`: to every day-`m` table, a probability on the day-`(m+1)` grid
whose restricted mean is the table (constraint 4), for every table in the unit cube. A junk
table (outside the cube) is not constrained. **No computability field** (see the module
docstring).
Source: bli-slides-017 constraints 4–5 as a map `t ↦ F⃗`; bli-soto-a-035; [[bli-program]] §2.4
Kind: D
Fidelity: variant: no `computable` field (disclosed) -/
structure Kernel (𝒮 : SmallIndex) (d : ℕ → ℕ) (m : ℕ) where
  /-- The superbelief about day `m+1` given the day-`m` table. -/
  law : Table 𝒮 m → Superbelief 𝒮 (m + 1)
  /-- Each law is a probability on the day-`(m+1)` grid. -/
  prob : ∀ t, IsProb d (law t)
  /-- Balance (constraint 4) for every table in the unit cube. -/
  balanced : ∀ t, t.InUnit → Balanced d (law t) t

/-- **Skeleton**: one kernel per day.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
structure Skeleton (𝒮 : SmallIndex) (d : ℕ → ℕ) where
  /-- The day-`m` kernel. -/
  κ : ∀ m, Kernel 𝒮 d m

variable {d : ℕ → ℕ}

/-- A table with positive kernel mass is a grid table, hence in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Kernel.inUnit_of_pos {m : ℕ} (κ : Kernel 𝒮 d m) {t : Table 𝒮 m} {Q : Table 𝒮 (m + 1)}
    (h : 0 < κ.law t Q) : Q.InUnit :=
  inUnit_of_mem_grid ((κ.prob t).mem_of_pos h)

/-- Kernel laws sum to one over the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Kernel.sum_law {m : ℕ} (κ : Kernel 𝒮 d m) (t : Table 𝒮 m) :
    ∑ Q ∈ grid 𝒮 d (m + 1), κ.law t Q = 1 := (κ.prob t).2.2

/-- Kernel laws are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Kernel.law_nonneg {m : ℕ} (κ : Kernel 𝒮 d m) (t : Table 𝒮 m) (Q : Table 𝒮 (m + 1)) :
    0 ≤ κ.law t Q := (κ.prob t).1 Q

/-- Kernel laws vanish off the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Kernel.law_eq_zero_of_not_mem {m : ℕ} (κ : Kernel 𝒮 d m) (t : Table 𝒮 m)
    {Q : Table 𝒮 (m + 1)} (h : Q ∉ grid 𝒮 d (m + 1)) : κ.law t Q = 0 := (κ.prob t).2.1 Q h

/-- Transport of a kernel evaluation along an equality of days (used by the chain rule).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Skeleton.law_castDay (sk : Skeleton 𝒮 d) {e e' : ℕ} (he : e = e') (s : Table 𝒮 e)
    (Q : Table 𝒮 (e + 1)) :
    (sk.κ e').law (s.castDay he) (Q.castDay (by rw [he])) = (sk.κ e).law s Q := by
  subst he; rfl

/-! ## Trajectories -/

/-- **Trajectory** of tables on days `n+1, …, n+h`, as a dependent tuple (snoc-oriented).
Source: [[bli-program]] §2.4 (`(∀ m ∈ Ioc n H, grid d m)`, with a better induction)
Kind: D
Fidelity: exact -/
def Traj (𝒮 : SmallIndex) (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | h + 1 => Traj 𝒮 n h × Table 𝒮 (n + h + 1)

namespace Traj

variable {n : ℕ}

/-- The last table of a trajectory started from `t` on day `n` (`t` itself for the empty
trajectory).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def last (t : Table 𝒮 n) : {h : ℕ} → Traj 𝒮 n h → Table 𝒮 (n + h)
  | 0, _ => t
  | _ + 1, (_, Q) => Q

/-- The last table of the empty trajectory is the start table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma last_zero (t : Table 𝒮 n) (τ : Traj 𝒮 n 0) : τ.last t = t := rfl

/-- The last table of a nonempty trajectory is its last component.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma last_succ (t : Table 𝒮 n) {h : ℕ} (τ : Traj 𝒮 n h) (Q : Table 𝒮 (n + h + 1)) :
    (show Traj 𝒮 n (h + 1) from (τ, Q)).last t = Q := rfl

/-- The table on an explicit day `m` with `n < m ≤ n + h`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def day : {h : ℕ} → Traj 𝒮 n h → (m : ℕ) → n < m → m ≤ n + h → Table 𝒮 m
  | 0, _, _, hm, hmh => absurd hmh (by omega)
  | h + 1, (τ, Q), m, hm, hmh =>
      if hme : m = n + h + 1 then Q.castDay hme.symm else τ.day m hm (by omega)

/-- The day-`(n+h+1)` table of a horizon-`(h+1)` trajectory is its last component.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma day_last {h : ℕ} (τ : Traj 𝒮 n h) (Q : Table 𝒮 (n + h + 1)) (hm : n < n + h + 1)
    (hmh : n + h + 1 ≤ n + (h + 1)) :
    (show Traj 𝒮 n (h + 1) from (τ, Q)).day (n + h + 1) hm hmh = Q := by
  simp [day]

/-- The day-`m` table of a horizon-`(h+1)` trajectory, for `m` before the last day, is read off the prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma day_of_ne {h : ℕ} (τ : Traj 𝒮 n h) (Q : Table 𝒮 (n + h + 1)) {m : ℕ} (hm : n < m)
    (hmh : m ≤ n + (h + 1)) (hne : m ≠ n + h + 1) :
    (show Traj 𝒮 n (h + 1) from (τ, Q)).day m hm hmh = τ.day m hm (by omega) := by
  simp [day, hne]

/-- Concatenation of a trajectory on days `n+1 … n+h` with one on days `n+h+1 … n+h+k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def append {h : ℕ} (τ : Traj 𝒮 n h) : {k : ℕ} → Traj 𝒮 (n + h) k → Traj 𝒮 n (h + k)
  | 0, _ => τ
  | k + 1, (τ', Q) =>
      show Traj 𝒮 n (h + k) × Table 𝒮 (n + (h + k) + 1) from (τ.append τ', Q.castDay (by omega))

/-- The last table of a concatenation is the last table of the second part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma last_append (t : Table 𝒮 n) {h : ℕ} (τ : Traj 𝒮 n h) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + h) k),
      (τ.append τ').last t = (τ'.last (τ.last t)).castDay (by omega)
  | 0, _ => rfl
  | _ + 1, (_, _) => rfl

end Traj

/-! ## The trajectory law -/

/-- **The trajectory law**: the Markov law of a trajectory of tables on days `n+1 … n+h` started
from `t` on day `n`, **defined by the recursion** `trajLaw (h+1) t (τ, Q) = trajLaw h t τ ·
κ_{n+h}(last τ)(Q)`. Its marginal on the state algebra is what `𝐏_n` is in the program.
Source: bli-soto-a-035 (chain rule as a definition); [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def trajLaw (sk : Skeleton 𝒮 d) (n : ℕ) : (h : ℕ) → Table 𝒮 n → Traj 𝒮 n h → ℚ
  | 0, _, _ => 1
  | h + 1, t, (τ, Q) => trajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q

/-- The finite carrier of day-`n` horizon-`h` trajectories: the product of the day grids.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def trajGrid (𝒮 : SmallIndex) (d : ℕ → ℕ) (n : ℕ) : (h : ℕ) → Finset (Traj 𝒮 n h)
  | 0 => {PUnit.unit}
  | h + 1 => trajGrid 𝒮 d n h ×ˢ grid 𝒮 d (n + h + 1)

variable (sk : Skeleton 𝒮 d) {n : ℕ}

/-- The empty trajectory has law `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma trajLaw_zero (t : Table 𝒮 n) (τ : Traj 𝒮 n 0) : trajLaw sk n 0 t τ = 1 := rfl

/-- The defining recursion of `trajLaw`, as a rewrite rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma trajLaw_succ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h) (Q : Table 𝒮 (n + h + 1)) :
    trajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) =
      trajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q := rfl

/-- The horizon-0 carrier is the singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma trajGrid_zero : trajGrid 𝒮 d n 0 = {PUnit.unit} := rfl

/-- The defining recursion of `trajGrid`, as a rewrite rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma trajGrid_succ (h : ℕ) :
    trajGrid 𝒮 d n (h + 1) = trajGrid 𝒮 d n h ×ˢ grid 𝒮 d (n + h + 1) := rfl

/-- Every horizon-0 trajectory is in the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_trajGrid_zero (τ : Traj 𝒮 n 0) : τ ∈ trajGrid 𝒮 d n 0 := by
  show τ ∈ ({PUnit.unit} : Finset PUnit)
  exact Finset.mem_singleton.mpr rfl

/-- Membership in the carrier, one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_trajGrid_succ {h : ℕ} {τ : Traj 𝒮 n h} {Q : Table 𝒮 (n + h + 1)} :
    (show Traj 𝒮 n (h + 1) from (τ, Q)) ∈ trajGrid 𝒮 d n (h + 1) ↔
      τ ∈ trajGrid 𝒮 d n h ∧ Q ∈ grid 𝒮 d (n + h + 1) :=
  Finset.mem_product

/-- Sums over the horizon-0 carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_trajGrid_zero (f : Traj 𝒮 n 0 → ℚ) : ∑ τ ∈ trajGrid 𝒮 d n 0, f τ = f PUnit.unit := by
  show ∑ τ ∈ ({PUnit.unit} : Finset PUnit), f τ = f PUnit.unit
  exact Finset.sum_singleton _ _

/-- Sums over the carrier, one step (Fubini on the product).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_trajGrid_succ {h : ℕ} (f : Traj 𝒮 n (h + 1) → ℚ) :
    ∑ τ ∈ trajGrid 𝒮 d n (h + 1), f τ =
      ∑ τ ∈ trajGrid 𝒮 d n h, ∑ Q ∈ grid 𝒮 d (n + h + 1), f (show Traj 𝒮 n (h + 1) from (τ, Q)) :=
  Finset.sum_product _ _ _

/-- The trajectory law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trajLaw_nonneg : ∀ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h), 0 ≤ trajLaw sk n h t τ
  | 0, _, _ => by simp
  | h + 1, t, (τ, Q) => by
      rw [trajLaw_succ]
      exact mul_nonneg (trajLaw_nonneg t τ) ((sk.κ (n + h)).law_nonneg _ _)

/-- The trajectory law vanishes off the product of the day grids.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trajLaw_support :
    ∀ {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h), τ ∉ trajGrid 𝒮 d n h → trajLaw sk n h t τ = 0
  | 0, _, τ, hτ => absurd (mem_trajGrid_zero τ) hτ
  | h + 1, t, (τ, Q), hτ => by
      have hτ' := mt mem_trajGrid_succ.mpr hτ
      rw [not_and_or] at hτ'
      rw [trajLaw_succ]
      rcases hτ' with hτ | hQ
      · rw [trajLaw_support t τ hτ, zero_mul]
      · rw [(sk.κ (n + h)).law_eq_zero_of_not_mem _ hQ, mul_zero]

/-- **Marginalizing the last day**: summing the horizon-`(h+1)` law over the last table gives the
horizon-`h` law.
Source: bli-soto-a-035; [[bli-program]] §2.4 (`trajLaw_marginal`)
Kind: L
Fidelity: exact -/
lemma trajLaw_marginal {h : ℕ} (t : Table 𝒮 n) (τ : Traj 𝒮 n h) :
    ∑ Q ∈ grid 𝒮 d (n + h + 1), trajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) =
      trajLaw sk n h t τ := by
  simp only [trajLaw_succ]
  rw [← Finset.mul_sum, (sk.κ (n + h)).sum_law, mul_one]

/-- **The trajectory law is a probability** on the product of the day grids.
Source: bli-slides-017 constraint 5 at every horizon; [[bli-program]] §3.5(i) (`trajLaw_isProb`)
Kind: L
Fidelity: exact -/
lemma trajLaw_sum_one : ∀ {h : ℕ} (t : Table 𝒮 n), ∑ τ ∈ trajGrid 𝒮 d n h, trajLaw sk n h t τ = 1
  | 0, _ => by rw [sum_trajGrid_zero]; rfl
  | h + 1, t => by
      rw [sum_trajGrid_succ]
      simp only [trajLaw_marginal]
      exact trajLaw_sum_one t

/-- `IsProbOn` packaging of `trajLaw_nonneg`, `trajLaw_support`, `trajLaw_sum_one`.
Source: [[bli-program]] §3.5(i)
Kind: L
Fidelity: exact -/
lemma trajLaw_isProbOn {h : ℕ} (t : Table 𝒮 n) :
    IsProbOn (trajGrid 𝒮 d n h) (trajLaw sk n h t) :=
  ⟨trajLaw_nonneg sk t, fun τ hτ => trajLaw_support sk t τ hτ, trajLaw_sum_one sk t⟩

/-- The last table of a grid trajectory started in the unit cube is in the unit cube (so
`Kernel.balanced` applies along the chain).
Source: none: infrastructure (mandate T6 `trajLaw_inUnit_step`)
Kind: L
Fidelity: n/a -/
lemma Traj.last_inUnit {t : Table 𝒮 n} (ht : t.InUnit) :
    ∀ {h : ℕ} {τ : Traj 𝒮 n h}, τ ∈ trajGrid 𝒮 d n h → (τ.last t).InUnit
  | 0, _, _ => ht
  | _ + 1, (_, _), hτ => inUnit_of_mem_grid (mem_trajGrid_succ.mp hτ).2

/-- **The Markov / chain rule**: the law of a concatenation factors as the law of the first part
times the law of the second part restarted from the first part's last table. `h = 1, k = 1`
is Soto's display `𝐏_{n-1}(𝐐_{n+1} = Q') = ∑_Q 𝐏^Q_n(𝐐_{n+1} = Q') 𝐏_{n-1}(𝐐_n = Q)` after
marginalizing (`trajLaw_two_marginal`).
Source: bli-soto-a-035 (Soto 04 p. 5); [[bli-program]] §2.4
Kind: P
Fidelity: exact
Hyps: (a) none -/
lemma trajLaw_chain (t : Table 𝒮 n) {h : ℕ} (τ : Traj 𝒮 n h) :
    ∀ {k : ℕ} (τ' : Traj 𝒮 (n + h) k),
      trajLaw sk n (h + k) t (τ.append τ') = trajLaw sk n h t τ * trajLaw sk (n + h) k (τ.last t) τ'
  | 0, _ => by
      show trajLaw sk n h t τ = trajLaw sk n h t τ * 1
      rw [mul_one]
  | k + 1, (τ', Q) => by
      show trajLaw sk n (h + k + 1) t (τ.append τ', Q.castDay (by omega)) = _
      rw [trajLaw_succ, trajLaw_chain t τ τ', trajLaw_succ, mul_assoc]
      congr 2
      rw [Traj.last_append]
      exact sk.law_castDay (by omega) _ _

/-- Soto's two-step display: the day-`(n+2)` marginal of the horizon-2 law is the composition of
the two one-step kernels.
Source: bli-soto-a-035 (Soto 04 p. 5)
Kind: L
Fidelity: exact -/
lemma trajLaw_two_marginal (t : Table 𝒮 n) (Q' : Table 𝒮 (n + 1 + 1)) :
    ∑ Q ∈ grid 𝒮 d (n + 1),
        trajLaw sk n 2 t (show Traj 𝒮 n 2 from ((PUnit.unit, Q), Q')) =
      ∑ Q ∈ grid 𝒮 d (n + 1), (sk.κ n).law t Q * (sk.κ (n + 1)).law Q Q' := by
  apply Finset.sum_congr rfl
  intro Q _
  show (1 * (sk.κ n).law t Q) * (sk.κ (n + 1)).law Q Q' = _
  rw [one_mul]

/-! ## The martingale property (constraint 4 at every horizon) -/

/-- Constraint 4 for the **last** table at every horizon: the expected day-`(n+h)` price of a
day-`n` small sentence is its day-`n` price.
Source: bli-paper-036 (the inventory's martingale consequence — ATTRIBUTION-UNVETTED as the
author's intent); proved here over the skeleton, where it is a theorem, not a stipulation
Kind: C
Fidelity: exact (in the program's object)
Hyps: (a) `t.InUnit` is the standing unit-cube hypothesis (junk tables are unconstrained) -/
lemma trajLaw_martingale_last {t : Table 𝒮 n} (ht : t.InUnit) (φ : ↥(𝒮.S n)) :
    ∀ (h : ℕ), ∑ τ ∈ trajGrid 𝒮 d n h,
      trajLaw sk n h t τ * τ.last t ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n h) φ.2⟩ = t φ
  | 0 => by rw [sum_trajGrid_zero, trajLaw_zero, Traj.last_zero, one_mul]; rfl
  | h + 1 => by
      rw [sum_trajGrid_succ]
      have step : ∀ τ ∈ trajGrid 𝒮 d n h,
          (∑ Q ∈ grid 𝒮 d (n + h + 1), trajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) *
            (show Traj 𝒮 n (h + 1) from (τ, Q)).last t
              ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n (h + 1)) φ.2⟩) =
          trajLaw sk n h t τ * τ.last t ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n h) φ.2⟩ := by
        intro τ hτ
        simp only [trajLaw_succ, Traj.last_succ]
        rw [show (∑ Q ∈ grid 𝒮 d (n + h + 1), trajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q *
            Q ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n (h + 1)) φ.2⟩) =
            trajLaw sk n h t τ * ∑ Q ∈ grid 𝒮 d (n + h + 1), (sk.κ (n + h)).law (τ.last t) Q *
              Q ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n (h + 1)) φ.2⟩ by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
        congr 1
        exact (sk.κ (n + h)).balanced _ (Traj.last_inUnit ht hτ)
          ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n h) φ.2⟩
      rw [Finset.sum_congr rfl step]
      exact trajLaw_martingale_last ht φ h

/-- **`trajLaw_martingale` (load-bearing).** Constraint 4 at every horizon and every intermediate
day: for a start table in the unit cube, a day-`n` small sentence `φ` and a day `m` with
`n < m ≤ n + h`, the expectation under the horizon-`h` trajectory law of the day-`m` price of
`φ` is its day-`n` price. This is bli-paper-036's "martingale consequence", which is the
inventory's derivation (ATTRIBUTION-UNVETTED as the paper's intent); the paper never says
whether `𝐏_n` is a measure on the state algebra — over the skeleton it is one by construction
(`trajLaw_isProbOn`), and the consequence is a theorem *in the program's object*. Not
"Appendix B's martingale property".
Source: bli-paper-036 (consequence); [[bli-program]] §2.4 (`trajLaw_martingale`)
Kind: C
Fidelity: exact (in the program's object)
Hyps: (a) `t.InUnit` (unit-cube standing hypothesis); (a) `n < m ≤ n + h` (day range) -/
theorem trajLaw_martingale {t : Table 𝒮 n} (ht : t.InUnit) (φ : ↥(𝒮.S n)) :
    ∀ {h : ℕ} (m : ℕ) (hm : n < m) (hmh : m ≤ n + h),
      ∑ τ ∈ trajGrid 𝒮 d n h,
        trajLaw sk n h t τ * τ.day m hm hmh ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩ = t φ
  | 0, m, hm, hmh => absurd hmh (by omega)
  | h + 1, m, hm, hmh => by
      rw [sum_trajGrid_succ]
      by_cases hme : m = n + h + 1
      · subst hme
        have step : ∀ τ ∈ trajGrid 𝒮 d n h,
            (∑ Q ∈ grid 𝒮 d (n + h + 1),
              trajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) *
                (show Traj 𝒮 n (h + 1) from (τ, Q)).day (n + h + 1) hm hmh
                  ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩) =
            trajLaw sk n h t τ * τ.last t ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n h) φ.2⟩ := by
          intro τ hτ
          simp only [trajLaw_succ, Traj.day_last]
          rw [show (∑ Q ∈ grid 𝒮 d (n + h + 1), trajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q *
              Q ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩) =
              trajLaw sk n h t τ * ∑ Q ∈ grid 𝒮 d (n + h + 1), (sk.κ (n + h)).law (τ.last t) Q *
                Q ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩ by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
          congr 1
          exact (sk.κ (n + h)).balanced _ (Traj.last_inUnit ht hτ)
            ⟨φ.1, 𝒮.mono_le (Nat.le_add_right n h) φ.2⟩
        rw [Finset.sum_congr rfl step]
        exact trajLaw_martingale_last sk ht φ h
      · have hmh' : m ≤ n + h := by omega
        have step : ∀ τ ∈ trajGrid 𝒮 d n h,
            (∑ Q ∈ grid 𝒮 d (n + h + 1),
              trajLaw sk n (h + 1) t (show Traj 𝒮 n (h + 1) from (τ, Q)) *
                (show Traj 𝒮 n (h + 1) from (τ, Q)).day m hm hmh ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩) =
            trajLaw sk n h t τ * τ.day m hm hmh' ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩ := by
          intro τ _
          simp only [trajLaw_succ, Traj.day_of_ne τ _ hm hmh hme]
          rw [show (∑ Q ∈ grid 𝒮 d (n + h + 1), trajLaw sk n h t τ * (sk.κ (n + h)).law (τ.last t) Q *
              τ.day m hm hmh' ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩) =
              trajLaw sk n h t τ * τ.day m hm hmh' ⟨φ.1, 𝒮.mono_le hm.le φ.2⟩ *
                ∑ Q ∈ grid 𝒮 d (n + h + 1), (sk.κ (n + h)).law (τ.last t) Q by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
          rw [(sk.κ (n + h)).sum_law, mul_one]
        rw [Finset.sum_congr rfl step]
        exact trajLaw_martingale ht φ m hm hmh'

end Cleanroom.Bli.BliFinite
