import Cleanroom.Bli.UdtBliCore.ProductUtil
import Cleanroom.Bli.BliFinite.Tent
import Cleanroom.Bli.BliFinite.Witness

/-!
# `udt-bli-core` · OfSkeleton: the prior built from a `bli-finite` skeleton, with derived faith
(T2, and the extension's abstract world law)

`ofSkeletonWith sk n h t W ν U` is the `FiniteBLIPrior` on
`Ω = ↥(trajGrid 𝒮 d n (h+1)) × W.World × Policy` with
`μ (τ, w, π) = trajLaw sk n (h+1) t τ · W.law (last τ) w · ν π`: the trajectory law of
`bli-finite` times the latest table's **world law** times an independent policy law. The decision
day is `m = n + h + 1` (horizon `h + 1`, so the last table is a grid table and `state` lands in
`𝒟 = grid 𝒮 d (n+h+1)`); `state (τ, w, π) = last τ`, `small (τ, w, π) = W.truth w`,
`pp (τ, w, π) = π`.

**Faith is derived**: the `faith` field of the prior is a theorem of the construction, proved
from the world law's marginal condition `∑_w W.law T w · [w ⊨ φ] = T φ`. The world law is
abstract (`WorldLaw`): the mandate's T2 is the **product** world law `productWorldLaw`
(`ofSkeleton`), the coherent world measure of `bli-finite`'s `IsWorldMarginal` is another
instance (extension, not built here). `t` needs no hypothesis: the horizon is `h + 1`, so every
outcome's last table is a grid table.

**The N+ witness** (`tentPrior`): the tent skeleton on `witIndex`, prior day `0`, horizon `1`,
`t = t₀ = (1/2)`, product world law, uniform independent points, actions `Bool`, and the utility
"bet on `p`" — `U = [w ⊨ p]` if the home point says `true`, `1 − [w ⊨ p]` if `false`. Then the
nine grid tables each have mass `1/9`, the prior is `Reflective`, `NoCrossBranch`,
`ReflectivePolicy`, `LocalUtility`, `IndependentPoints`, `FaithGivenPoints`, satisfies `NDPOL`,
`NDHOME`, `NDPOLICY`, and its updateful values are the **table's own prices**:
`homeEU T true = T p`, `homeEU T false = 1 − T p`, so the updateful maximizer varies across
positive-mass tables (`(1, ·)` bets `true`, `(0, ·)` bets `false`). This is the inhabitant of
T5's and T6's hypothesis packages with content.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-! ## World laws -/

/-- **An abstract world law over the day-`m` tables**: a finite world type with a truth assignment
to the small sentences, a law per table, nonnegative on unit-cube tables, of mass one, and
**marginally faithful**: `∑_w law T w · [w ⊨ φ] = T φ`. The only hypothesis the derived faith of
`ofSkeletonWith` needs.
Source: mandate T12 extension ("an abstract per-table world law with the marginal condition as
the only hypothesis"); [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
structure WorldLaw (𝒮 : SmallIndex) (m : ℕ) where
  /-- The worlds. -/
  World : Type
  [fin : Fintype World]
  /-- The truth of each small sentence in each world. -/
  truth : World → ↥(𝒮.S m) → Bool
  /-- The law of worlds under each table. -/
  law : Table 𝒮 m → World → ℚ
  /-- Nonnegativity on unit-cube tables. -/
  nonneg : ∀ T : Table 𝒮 m, T.InUnit → ∀ w, 0 ≤ law T w
  /-- Mass one. -/
  sum_one : ∀ T : Table 𝒮 m, ∑ w, law T w = 1
  /-- The marginal condition. -/
  marginal : ∀ (T : Table 𝒮 m) (φ : ↥(𝒮.S m)), ∑ w, law T w * ind (truth w φ) = T φ

attribute [instance] WorldLaw.fin

/-- The coordinate weights of the product world law: `T φ` on `true`, `1 − T φ` on `false`.
Source: mandate T2 (`Π_φ (if w φ then T φ else 1 − T φ)`)
Kind: D
Fidelity: exact -/
def worldWeight {𝒮 : SmallIndex} {m : ℕ} (T : Table 𝒮 m) (φ : ↥(𝒮.S m)) (b : Bool) : ℚ :=
  if b then T φ else 1 - T φ

/-- The coordinate weights sum to one (for every table).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldWeight_sum {𝒮 : SmallIndex} {m : ℕ} (T : Table 𝒮 m) (φ : ↥(𝒮.S m)) :
    ∑ b, worldWeight T φ b = 1 := by
  simp [worldWeight, Fintype.sum_bool]

/-- **The product world law**: worlds are truth assignments to the day-`m` small sentences,
independent across sentences with `P(φ true) = T φ`.
Source: mandate T2 ("the latest table's **product** world measure")
Kind: D
Fidelity: variant: product world measure (disclosed; the coherent measure is the extension) -/
def productWorldLaw (𝒮 : SmallIndex) (m : ℕ) : WorldLaw 𝒮 m where
  World := ↥(𝒮.S m) → Bool
  truth := fun w => w
  law := fun T w => prodLaw (worldWeight T) w
  nonneg := fun T hT w => prodLaw_nonneg (fun φ b => by
    unfold worldWeight
    split_ifs
    · exact (hT φ).1
    · linarith [(hT φ).2]) w
  sum_one := fun T => sum_prodLaw (worldWeight_sum T)
  marginal := fun T φ => by
    rw [sum_prodLaw_mul_fun (worldWeight_sum T) φ ind]
    simp [Fintype.sum_bool, worldWeight]

/-! ## The construction -/

section Construction

variable {𝒮 : SmallIndex} {d : ℕ → ℕ} (sk : Skeleton 𝒮 d) (n h : ℕ) (t : Table 𝒮 n)

/-- The last table of a horizon-`(h+1)` trajectory, read off the product structure.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def lastOf (σ : Traj 𝒮 n (h + 1)) : Table 𝒮 (n + h + 1) :=
  (show Traj 𝒮 n h × Table 𝒮 (n + h + 1) from σ).2

/-- `Traj.last t σ = lastOf σ` at horizon `h + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma last_eq_lastOf (σ : Traj 𝒮 n (h + 1)) : σ.last t = lastOf n h σ := rfl

/-- The last table of a grid trajectory is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lastOf_mem_grid {σ : Traj 𝒮 n (h + 1)} (hσ : σ ∈ trajGrid 𝒮 d n (h + 1)) :
    lastOf n h σ ∈ grid 𝒮 d (n + h + 1) :=
  (mem_trajGrid_succ (τ := (show Traj 𝒮 n h × Table 𝒮 (n + h + 1) from σ).1)
    (Q := (show Traj 𝒮 n h × Table 𝒮 (n + h + 1) from σ).2)).mp hσ |>.2

variable (W : WorldLaw 𝒮 (n + h + 1))

/-- The state coordinate: the last table, as an element of the decision-day grid.
Source: mandate T2 (`state (τ, w) := τ.last t`, valued in `𝒟`)
Kind: D
Fidelity: exact -/
def skelState (σ : ↥(trajGrid 𝒮 d n (h + 1))) : ↥(grid 𝒮 d (n + h + 1)) :=
  ⟨lastOf n h σ.1, lastOf_mem_grid n h σ.2⟩

/-- The base law: trajectory law times the last table's world law.
Source: [[bli-program]] §2.8 ("`ofSkeleton` = `trajLaw` ⊗ the latest table's measure")
Kind: D
Fidelity: exact -/
def skelBase (ω : ↥(trajGrid 𝒮 d n (h + 1)) × W.World) : ℚ :=
  trajLaw sk n (h + 1) t ω.1.1 * W.law (lastOf n h ω.1.1) ω.2

/-- The base law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma skelBase_nonneg (ω : ↥(trajGrid 𝒮 d n (h + 1)) × W.World) : 0 ≤ skelBase sk n h t W ω :=
  mul_nonneg (trajLaw_nonneg sk t _)
    (W.nonneg _ (inUnit_of_mem_grid (lastOf_mem_grid n h ω.1.2)) ω.2)

/-- The base law has mass one (`trajLaw_sum_one` and the world law's mass one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma skelBase_sum_one : ∑ ω, skelBase sk n h t W ω = 1 := by
  unfold skelBase
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, W.sum_one, mul_one]
  rw [Finset.sum_coe_sort (trajGrid 𝒮 d n (h + 1)) (fun σ => trajLaw sk n (h + 1) t σ)]
  exact trajLaw_sum_one sk t

/-- **Derived faith of the base**: from the world law's marginal condition.
Source: mandate T2 ("derived faith: the field is a theorem of the construction")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem skelBase_faith (T : ↥(grid 𝒮 d (n + h + 1))) (φ : ↥(𝒮.S (n + h + 1))) :
    integralOf (skelBase sk n h t W) (fun ω => ind (W.truth ω.2 φ))
        (fun ω => skelState (d := d) n h ω.1 = T) =
      T.1 φ * massOf (skelBase sk n h t W) (fun ω => skelState (d := d) n h ω.1 = T) := by
  unfold integralOf massOf
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : skelState (d := d) n h σ = T
  · simp only [hσ, if_true]
    unfold skelBase
    have hT : lastOf n h σ.1 = T.1 := by rw [← hσ]; rfl
    simp only [hT, mul_assoc, ← Finset.mul_sum]
    rw [W.marginal T.1 φ, W.sum_one]
    ring
  · simp [hσ]

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The independent-policy data of a skeleton**: the base above with a policy law `ν` and a
utility `U` reading the outcome and the policy.
Source: [[bli-program]] §2.8; mandate T2
Kind: D
Fidelity: exact -/
def skelData (ν : Policy (grid 𝒮 d (n + h + 1)) A → ℚ) (hν : ∀ π, 0 ≤ ν π)
    (hν1 : ∑ π, ν π = 1)
    (U : ↥(trajGrid 𝒮 d n (h + 1)) × W.World → Policy (grid 𝒮 d (n + h + 1)) A → ℚ) :
    IndepData 𝒮 (n + h + 1) (grid 𝒮 d (n + h + 1)) A where
  Ω₀ := ↥(trajGrid 𝒮 d n (h + 1)) × W.World
  μ₀ := skelBase sk n h t W
  μ₀_nonneg := skelBase_nonneg sk n h t W
  μ₀_sum_one := skelBase_sum_one sk n h t W
  state₀ := fun ω => skelState n h ω.1
  small₀ := fun ω => W.truth ω.2
  faith₀ := skelBase_faith sk n h t W
  ν := ν
  ν_nonneg := hν
  ν_sum_one := hν1
  U₀ := U

/-- **`ofSkeletonWith`**: the prior of a skeleton with an abstract world law (definition of record;
the extension's general form).
Source: mandate T12 extension; [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
def ofSkeletonWith (ν : Policy (grid 𝒮 d (n + h + 1)) A → ℚ) (hν : ∀ π, 0 ≤ ν π)
    (hν1 : ∑ π, ν π = 1)
    (U : ↥(trajGrid 𝒮 d n (h + 1)) × W.World → Policy (grid 𝒮 d (n + h + 1)) A → ℚ) :
    FiniteBLIPrior 𝒮 (n + h + 1) (grid 𝒮 d (n + h + 1)) A :=
  (skelData sk n h t W ν hν hν1 U).toPrior

/-- **`ofSkeleton`**: the prior of a skeleton with the product world law (definition of record,
T2).
Source: [[bli-program]] §2.8 ("`ofSkeleton` = `trajLaw` ⊗ the latest table's measure");
mandate T2
Kind: D
Fidelity: variant: product world measure (disclosed) -/
def ofSkeleton (ν : Policy (grid 𝒮 d (n + h + 1)) A → ℚ) (hν : ∀ π, 0 ≤ ν π)
    (hν1 : ∑ π, ν π = 1)
    (U : ↥(trajGrid 𝒮 d n (h + 1)) × (↥(𝒮.S (n + h + 1)) → Bool) →
      Policy (grid 𝒮 d (n + h + 1)) A → ℚ) :
    FiniteBLIPrior 𝒮 (n + h + 1) (grid 𝒮 d (n + h + 1)) A :=
  ofSkeletonWith sk n h t (productWorldLaw 𝒮 (n + h + 1)) ν hν hν1 U

/-- **Faith of `ofSkeleton` is a theorem of the construction** (the field, restated): within
each table's branch the frequency of every small sentence is the table's price, because the world
coordinate is drawn from the product measure of the last table.
Source: mandate T2 ("derived faith"); [[bli-program]] §2.8
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ofSkeleton_faith (ν : Policy (grid 𝒮 d (n + h + 1)) A → ℚ) (hν : ∀ π, 0 ≤ ν π)
    (hν1 : ∑ π, ν π = 1)
    (U : ↥(trajGrid 𝒮 d n (h + 1)) × (↥(𝒮.S (n + h + 1)) → Bool) →
      Policy (grid 𝒮 d (n + h + 1)) A → ℚ)
    (T : ↥(grid 𝒮 d (n + h + 1))) (φ : ↥(𝒮.S (n + h + 1))) :
    integralOf (ofSkeleton sk n h t ν hν hν1 U).μ
        (fun ω => ind ((ofSkeleton sk n h t ν hν hν1 U).small ω φ))
        (fun ω => (ofSkeleton sk n h t ν hν hν1 U).state ω = T) =
      T.1 φ * (ofSkeleton sk n h t ν hν hν1 U).stateMass T :=
  (ofSkeleton sk n h t ν hν hν1 U).faith T φ

/-- The state mass of `ofSkeletonWith` is the trajectory law's mass on the fiber of the last
table: `∑_{τ ∈ trajGrid, last τ = T} trajLaw τ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_ofSkeletonWith (ν : Policy (grid 𝒮 d (n + h + 1)) A → ℚ) (hν : ∀ π, 0 ≤ ν π)
    (hν1 : ∑ π, ν π = 1)
    (U : ↥(trajGrid 𝒮 d n (h + 1)) × W.World → Policy (grid 𝒮 d (n + h + 1)) A → ℚ)
    (T : ↥(grid 𝒮 d (n + h + 1))) :
    (ofSkeletonWith sk n h t W ν hν hν1 U).stateMass T =
      ∑ σ ∈ trajGrid 𝒮 d n (h + 1), if lastOf n h σ = T.1 then trajLaw sk n (h + 1) t σ else 0 := by
  unfold ofSkeletonWith
  rw [(skelData sk n h t W ν hν hν1 U).stateMass_toPrior]
  change massOf (skelBase sk n h t W) (fun ω => skelState (d := d) n h ω.1 = T) = _
  unfold massOf
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (trajGrid 𝒮 d n (h + 1))
    (fun σ => if lastOf n h σ = T.1 then trajLaw sk n (h + 1) t σ else 0)]
  apply Finset.sum_congr rfl
  intro σ _
  have hiff : skelState (d := d) n h σ = T ↔ lastOf n h σ.1 = T.1 := by
    constructor
    · intro h'; rw [← h']; rfl
    · intro h'; exact Subtype.ext h'
  by_cases hσ : lastOf n h σ.1 = T.1
  · simp only [hiff, hσ, if_true]
    unfold skelBase
    show ∑ w, trajLaw sk n (h + 1) t σ.1 * W.law (lastOf n h σ.1) w = trajLaw sk n (h + 1) t σ.1
    rw [← Finset.mul_sum, W.sum_one, mul_one]
  · simp [hiff, hσ]

/-- The conditional expectation on a branch of a function of the world alone is the world law's
expectation under that table, when the branch has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_world_ofSkeletonWith (F : W.World → ℚ) (T : ↥(grid 𝒮 d (n + h + 1)))
    (hT : 0 < massOf (skelBase sk n h t W) (fun ω => skelState (d := d) n h ω.1 = T)) :
    condExp (skelBase sk n h t W) (fun ω => F ω.2) (fun ω => skelState (d := d) n h ω.1 = T) =
      ∑ w, W.law T.1 w * F w := by
  unfold condExp
  rw [div_eq_iff (ne_of_gt hT)]
  unfold integralOf massOf
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : skelState (d := d) n h σ = T
  · simp only [hσ, if_true]
    unfold skelBase
    have hTσ : lastOf n h σ.1 = T.1 := by rw [← hσ]; rfl
    show ∑ w, trajLaw sk n (h + 1) t σ.1 * W.law (lastOf n h σ.1) w * F w =
      (∑ w, W.law T.1 w * F w) * ∑ w, trajLaw sk n (h + 1) t σ.1 * W.law (lastOf n h σ.1) w
    rw [hTσ, ← Finset.mul_sum, W.sum_one, mul_one, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    ring
  · simp [hσ]

end Construction

/-! ## The tent witness -/

namespace Tent

/-- The sentence `p` as an element of the day-1 small index of `witIndex`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev pW1 : ↥(witIndex.S 1) := ⟨pW, pW_mem_S1⟩

/-- The uniform coordinate weights `1/2` on both actions.
Source: mandate T2
Kind: D
Fidelity: exact -/
def tentHalf : ↥(grid witIndex witMesh.d 1) → Bool → ℚ := fun _ _ => 1 / 2

/-- The coordinate weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentHalf_sum : ∀ T, ∑ a, tentHalf T a = 1 := by
  intro T; norm_num [tentHalf, Fintype.sum_bool]

/-- **The bet-on-`p` utility**: `1` if the bet placed by the home point is right about `p` in the
world, `0` otherwise (`true` bets `p`, `false` bets `¬p`).
Source: mandate T2 ("a `U` and `pp` chosen so that … a varying updateful argmax")
Kind: D
Fidelity: exact -/
def betOnP (w : ↥(witIndex.S 1) → Bool) (a : Bool) : ℚ :=
  if a then ind (w pW1) else 1 - ind (w pW1)

/-- The decision day of the tent witness is `0 + 0 + 1 = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma day_eq : (0 : ℕ) + 0 + 1 = 1 := rfl

/-- The world type of the product world law on day 1 of `witIndex`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev TentWorld : Type := ↥(witIndex.S 1) → Bool

/-- The tent witness's utility as a function of the outcome and the policy: the bet placed at
the home point, judged in the world.
Source: mandate T2
Kind: D
Fidelity: exact -/
def tentU (ω : ↥(trajGrid witIndex witMesh.d 0 1) × TentWorld)
    (π : Policy (grid witIndex witMesh.d 1) Bool) : ℚ :=
  betOnP ω.2 (π (skelState (d := witMesh.d) 0 0 ω.1))

/-- **The tent data**: tent skeleton on `witIndex`, prior day 0, horizon 1, `t₀ = (1/2)`, product
world law, uniform independent points, bet-on-`p` utility.
Source: mandate T2
Kind: D
Fidelity: exact -/
def tentData : IndepData witIndex 1 (grid witIndex witMesh.d 1) Bool :=
  skelData (tentSkeleton witIndex witMesh) 0 0 t₀ (productWorldLaw witIndex 1)
    (prodLaw tentHalf) (prodLaw_nonneg (fun _ _ => by simp [tentHalf]))
    (sum_prodLaw tentHalf_sum) tentU

/-- **The tent prior** (the N+ witness of record for T5 and T6).
Source: mandate T2
Kind: D
Fidelity: exact -/
def tentPrior : FiniteBLIPrior witIndex 1 (grid witIndex witMesh.d 1) Bool := tentData.toPrior

/-- The home-only shape of the tent utility.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentU_home : ∀ (ω : tentData.Ω₀) (π : Policy (grid witIndex witMesh.d 1) Bool),
    tentData.U₀ ω π = betOnP ω.2 (π (tentData.state₀ ω)) := fun _ _ => rfl

/-- Every point weight is `1/2 > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentHalf_pos (T : ↥(grid witIndex witMesh.d 1)) (a : Bool) : 0 < tentHalf T a := by
  simp [tentHalf]

/-- **Every grid table has mass `1/9` under the tent prior** (nine positive-mass tables).
Source: mandate T2 ("nine positive-mass tables, `tentLaw_t₀_pos`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem stateMass_tentPrior (T : ↥(grid witIndex witMesh.d 1)) : tentPrior.stateMass T = 1 / 9 := by
  show (ofSkeletonWith (tentSkeleton witIndex witMesh) 0 0 t₀ (productWorldLaw witIndex 1)
    (prodLaw tentHalf) (prodLaw_nonneg (fun _ _ => by simp [tentHalf])) (sum_prodLaw tentHalf_sum)
    tentU).stateMass T = 1 / 9
  rw [stateMass_ofSkeletonWith (tentSkeleton witIndex witMesh) 0 0 t₀ (productWorldLaw witIndex 1)
    (prodLaw tentHalf) _ _ tentU T]
  rw [sum_trajGrid_succ, sum_trajGrid_zero]
  have e : ∀ Q ∈ grid witIndex witMesh.d 1,
      (if lastOf 0 0 (show Traj witIndex 0 1 from (PUnit.unit, Q)) = T.1 then
        trajLaw (tentSkeleton witIndex witMesh) 0 1 t₀ (show Traj witIndex 0 1 from (PUnit.unit, Q))
        else 0) = if Q = T.1 then tentLaw witMesh 0 t₀ Q else 0 := by
    intro Q _
    have h1 : lastOf 0 0 (show Traj witIndex 0 1 from (PUnit.unit, Q)) = Q := rfl
    have h2 : trajLaw (tentSkeleton witIndex witMesh) 0 1 t₀
        (show Traj witIndex 0 1 from (PUnit.unit, Q)) = tentLaw witMesh 0 t₀ Q := by
      rw [trajLaw_succ, trajLaw_zero, Traj.last_zero, one_mul]
      rfl
    rw [h1, h2]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (grid witIndex witMesh.d 1) T.1, if_pos T.2]
  exact tentLaw_t₀ T.2

/-- The base branch mass of every table is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMass_pos (T : ↥(grid witIndex witMesh.d 1)) :
    0 < massOf tentData.μ₀ (fun ω => tentData.state₀ ω = T) := by
  have := stateMass_tentPrior T
  unfold tentPrior at this
  rw [tentData.stateMass_toPrior] at this
  rw [this]; norm_num

/-- **The updateful value of betting `true` at `T` is `T p`**, the table's own price of `p`
(faith in action).
Source: mandate T2; bli-soto-a-011 ("the consequences of an action within its own branch should
just be the updateful picture")
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (the world law's marginal) -/
theorem homeEU_true (T : ↥(grid witIndex witMesh.d 1)) : tentPrior.homeEU T true = T.1 pW1 := by
  have h1 := tentData.homeEU_home tentHalf tentHalf_sum rfl (fun ω a => betOnP ω.2 a) tentU_home
    T true (tentHalf_pos T true)
  have h2 := condExp_world_ofSkeletonWith (tentSkeleton witIndex witMesh) 0 0 t₀
    (productWorldLaw witIndex 1) (fun w => betOnP w true) T (baseMass_pos T)
  have h3 : ∑ w : (productWorldLaw witIndex 1).World,
      (productWorldLaw witIndex 1).law T.1 w * ind (w pW1) = T.1 pW1 :=
    (productWorldLaw witIndex 1).marginal T.1 pW1
  unfold tentPrior
  rw [h1]
  refine h2.trans ?_
  simpa [betOnP] using h3

/-- **The updateful value of betting `false` at `T` is `1 − T p`.**
Source: mandate T2
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith -/
theorem homeEU_false (T : ↥(grid witIndex witMesh.d 1)) :
    tentPrior.homeEU T false = 1 - T.1 pW1 := by
  have h1 := tentData.homeEU_home tentHalf tentHalf_sum rfl (fun ω a => betOnP ω.2 a) tentU_home
    T false (tentHalf_pos T false)
  have h2 := condExp_world_ofSkeletonWith (tentSkeleton witIndex witMesh) 0 0 t₀
    (productWorldLaw witIndex 1) (fun w => betOnP w false) T (baseMass_pos T)
  have hm : ∑ w : (productWorldLaw witIndex 1).World,
      (productWorldLaw witIndex 1).law T.1 w * ind (w pW1) = T.1 pW1 :=
    (productWorldLaw witIndex 1).marginal T.1 pW1
  have hs := (productWorldLaw witIndex 1).sum_one T.1
  unfold tentPrior
  rw [h1]
  refine h2.trans ?_
  simp only [betOnP, Bool.false_eq_true, if_false, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hs, hm]

/-- The updateful maximizer at `T` is `true` iff `1/2 ≤ T p`.
Source: mandate T2
Kind: L
Fidelity: n/a -/
lemma isUpdatefulChoice_true_iff (T : ↥(grid witIndex witMesh.d 1)) :
    tentPrior.IsUpdatefulChoice T true ↔ 1 / 2 ≤ T.1 pW1 := by
  unfold FiniteBLIPrior.IsUpdatefulChoice
  constructor
  · intro h
    have := h false
    rw [homeEU_true, homeEU_false] at this
    linarith
  · intro h b
    cases b
    · rw [homeEU_true, homeEU_false]; linarith
    · exact le_rfl

/-- The updateful maximizer at `T` is `false` iff `T p ≤ 1/2`.
Source: mandate T2
Kind: L
Fidelity: n/a -/
lemma isUpdatefulChoice_false_iff (T : ↥(grid witIndex witMesh.d 1)) :
    tentPrior.IsUpdatefulChoice T false ↔ T.1 pW1 ≤ 1 / 2 := by
  unfold FiniteBLIPrior.IsUpdatefulChoice
  constructor
  · intro h
    have := h true
    rw [homeEU_true, homeEU_false] at this
    linarith
  · intro h b
    cases b
    · exact le_rfl
    · rw [homeEU_true, homeEU_false]; linarith

/-- The grid table `(p ↦ 1, q ↦ 1/2)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Qone : Table witIndex 1 := fun φ => if φ.1 = pW then 1 else 1 / 2

/-- `Qone` is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Qone_mem_grid : Qone ∈ grid witIndex witMesh.d 1 := by
  rw [mem_grid_iff]
  intro φ
  unfold Qone
  split_ifs
  · exact one_mem_gridVals (by norm_num [witMesh])
  · exact half_mem_gridVals_two

/-- The two tables on which the updateful maximizer differs.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Tone : ↥(grid witIndex witMesh.d 1) := ⟨Qone, Qone_mem_grid⟩

/-- The table `(p ↦ 0, q ↦ 1/2)` of `bli-finite` as a grid element.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Tzero : ↥(grid witIndex witMesh.d 1) := ⟨Q₂, Q₂_mem_grid⟩

/-- **The tent prior's structural predicates all hold**: `Reflective`, `NoCrossBranch`,
`ReflectivePolicy`, `LocalUtility`, `IndependentPoints`, `IndependentPointsGivenState`,
`FaithGivenPoints`, and the three positivity predicates.
Source: mandate T2 ("the tent prior is `Reflective ∧ NoCrossBranch`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tentPrior_structure :
    tentPrior.Reflective ∧ tentPrior.NoCrossBranch ∧ tentPrior.ReflectivePolicy ∧
      tentPrior.LocalUtility ∧ tentPrior.IndependentPoints ∧
      tentPrior.IndependentPointsGivenState ∧ tentPrior.FaithGivenPoints ∧
      tentPrior.NDPOL ∧ tentPrior.NDHOME ∧ tentPrior.NDPOLICY := by
  refine ⟨tentData.reflective_toPrior,
    tentData.noCrossBranch_home tentHalf tentHalf_sum rfl (fun ω a => betOnP ω.2 a) tentU_home,
    tentData.reflectivePolicy_toPrior,
    tentData.localUtility_home tentHalf tentHalf_sum rfl (fun ω a => betOnP ω.2 a) tentU_home,
    tentData.independentPoints_toPrior_of_prodLaw tentHalf tentHalf_sum rfl,
    tentData.independentPointsGivenState_toPrior_of_prodLaw tentHalf tentHalf_sum rfl,
    tentData.faithGivenPoints_toPrior, ?_, ?_, ?_⟩
  · exact tentData.ndpol_toPrior (fun T a => by
      change 0 < massOf (prodLaw tentHalf) (fun π => π T = a)
      rw [IndepData.massOf_prodLaw_point tentHalf tentHalf_sum]; exact tentHalf_pos T a)
  · exact tentData.ndhome_toPrior baseMass_pos (fun T a => by
      change 0 < massOf (prodLaw tentHalf) (fun π => π T = a)
      rw [IndepData.massOf_prodLaw_point tentHalf tentHalf_sum]; exact tentHalf_pos T a)
  · exact tentData.ndpolicy_toPrior (fun π => prodLaw_pos (fun _ _ => by simp [tentHalf]) π)

/-- **The updateful maximizer varies across positive-mass tables**: at `(1, 1/2)` only `true`
is updateful-optimal, at `(0, 1/2)` only `false`; both tables have mass `1/9`. Hence no single
action is an updateful choice at every positive-mass table (the strictness condition of Good's
theorem).
Source: mandate T2 ("a **varying** updateful argmax across positive-mass tables"); T6(iii)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tentPrior_varying :
    tentPrior.IsUpdatefulChoice Tone true ∧ ¬ tentPrior.IsUpdatefulChoice Tone false ∧
      tentPrior.IsUpdatefulChoice Tzero false ∧ ¬ tentPrior.IsUpdatefulChoice Tzero true ∧
      ¬ ∃ a, ∀ T, 0 < tentPrior.stateMass T → tentPrior.IsUpdatefulChoice T a := by
  have h1 : Tone.1 pW1 = 1 := by simp [Qone]
  have h0 : Tzero.1 pW1 = 0 := by simp [Q₂]
  refine ⟨(isUpdatefulChoice_true_iff Tone).mpr (by rw [h1]; norm_num),
    fun h => by have := (isUpdatefulChoice_false_iff Tone).mp h; rw [h1] at this; norm_num at this,
    (isUpdatefulChoice_false_iff Tzero).mpr (by rw [h0]; norm_num),
    fun h => by have := (isUpdatefulChoice_true_iff Tzero).mp h; rw [h0] at this; norm_num at this,
    ?_⟩
  rintro ⟨a, ha⟩
  cases a
  · have := (isUpdatefulChoice_false_iff Tone).mp (ha Tone (by rw [stateMass_tentPrior]; norm_num))
    rw [h1] at this; norm_num at this
  · have := (isUpdatefulChoice_true_iff Tzero).mp (ha Tzero (by rw [stateMass_tentPrior]; norm_num))
    rw [h0] at this; norm_num at this

end Tent

end Cleanroom.Bli.UdtBliCore
