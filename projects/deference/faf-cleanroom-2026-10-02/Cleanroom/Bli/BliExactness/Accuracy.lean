import Cleanroom.Bli.BliFinite.Tent
import Cleanroom.Bli.BliTrajectory.Degenerate

/-!
# `bli-exactness` — X7 (exact): expected future accuracy under exact faith

**FAF-free over `bli-finite`** (tables, grids, superbeliefs, kernels). Abram's b.415–422: the
Bayesian "trust your prior" argument (the prior minimizes expected proper-scoring error under
itself) fails for an agent that "can prefer what it would think soon". Made precise over the
finite trajectory prior: for a day-`(m+1)` superbelief `F` that is a probability on the grid and
balanced at the day-`m` table `t` (constraint 4), and a day-`m` coordinate `φ` read on day `m+1`,
with the Brier score and constraint 2 (the conditional probability of `φ` given the future state
`Q` is `Q φ`):

* `currentErr F t φ − futureErr F φ = ∑_Q F Q · (Q φ)² − (t φ)² = Var_F(Q φ)` (`accuracy_gap`,
  `accuracy_gap_eq_var`); the step `∑_Q F Q · Q φ = t φ` **is** `Balanced`, never a hypothesis.
* Hence `futureErr ≤ currentErr`, with equality iff `Q φ = t φ` `F`-a.s.
* Instances: the tent kernel from an interior table has a strictly positive gap (N+); B0's point
  mass has gap `0`.

**The finding's sentence**, with its register (audit r1 N3): the identity is the law of total
variance for a balanced kernel — a textbook Bayesian *also* expects her posterior to score better
than her prior under her prior, and b.417's "the prior minimizes the expected error" is about
forecasts available *now*. So: "trust your prior" holds exactly for the degenerate solution and
fails exactly when the kernel is uncertain about its own next price — **in b.419's sense that the
agent can already describe the better forecast (its own next price) and prefer it**, by the
kernel's variance of that price. That this is "bli-paper-2-013 (b) made precise" is an
attribution claim about the note's intent: ATTRIBUTION-UNVETTED (the inventory marks 2-013 (b) as
its writer's own formulation, "not in the source"); bli-paper-2-012's "variability" quantified as
`priceVar` is the package's reading.

Fidelity `variant`: "`𝔼ₙ`" is the state-partition sum `bli-trajectory` disclosed for
`marginalMass`; the Brier integrand uses constraint 2 (`ValueFaith for 𝟙(φ)`, construction row
C8) as the identification of `P(φ | Q)` with `Q φ`. The LI form (over `liaHistory`) is `stretch`
and not attempted here (report).
-/

namespace Cleanroom.Bli.BliExactness

open Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory Finset

variable {𝒮 : SmallIndex} {m : ℕ}

/-- A day-`m` coordinate read on day `m+1` (the index `Table.restrict` uses).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def coord (φ : ↥(𝒮.S m)) : ↥(𝒮.S (m + 1)) := ⟨φ.1, 𝒮.mono m φ.2⟩

/-- **The Brier integrand**: the expected squared error of the forecast `x` for `φ` when `φ` is
true with probability `q`: `q·(x−1)² + (1−q)·x²`.
Source: bli-paper-2-013 (a) (proper scoring rule, Brier)
Kind: D
Fidelity: exact (Brier) -/
def brier (q x : ℚ) : ℚ := q * (x - 1) ^ 2 + (1 - q) * x ^ 2

/-- `brier q x − brier q q = (q − x)²`: the excess Brier loss of forecasting `x` when the truth
probability is `q` is the squared distance to `q` (strict propriety of the Brier score, in the
form used here).
Source: bli-paper-2-013 (a) (folklore: Brier is strictly proper)
Kind: L
Fidelity: exact -/
lemma brier_sub_brier_self (q x : ℚ) : brier q x - brier q q = (q - x) ^ 2 := by
  unfold brier; ring

/-- **Expected future Brier error** of `φ` under `F`: the future price `Q φ` scored against `φ`,
whose probability given the state `Q` is `Q φ` (constraint 2), averaged over `F`.
Source: bli-paper-2-013 (b) ("`𝔼ₙ[(ℙ_{f(n)}(φ) − φ)²]`"); mandate X7 (exact)
Kind: D
Fidelity: variant: the finite state-partition expectation of `bli-trajectory` -/
def futureErr (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (φ : ↥(𝒮.S m)) : ℚ :=
  ∑ Q ∈ grid 𝒮 d (m + 1), F Q * brier (Q (coord φ)) (Q (coord φ))

/-- **Expected current Brier error** of the day-`m` price `t φ`, with the truth of `φ` drawn through
the future state (constraint 2 again).
Source: bli-paper-2-013 (b) ("`𝔼ₙ[(ℙₙ(φ) − φ)²]`"); mandate X7 (exact)
Kind: D
Fidelity: variant: as `futureErr` -/
def currentErr (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) : ℚ :=
  ∑ Q ∈ grid 𝒮 d (m + 1), F Q * brier (Q (coord φ)) (t φ)

/-- **The kernel's variance of its own next price** of `φ` around the current price `t φ`.
Source: bli-paper-2-013 (b) ("the market's expected variance of its own future price");
bli-paper-2-012 ("variability")
Kind: D
Fidelity: exact -/
def priceVar (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) : ℚ :=
  ∑ Q ∈ grid 𝒮 d (m + 1), F Q * (Q (coord φ) - t φ) ^ 2

/-- **The accuracy gap is the variance**: `currentErr − futureErr = priceVar`, for every `F`
(no hypothesis: termwise `brier_sub_brier_self`).
Source: bli-paper-2-013 (b); mandate X7 (exact)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem accuracy_gap_eq_var (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (t : Table 𝒮 m)
    (φ : ↥(𝒮.S m)) : currentErr d F t φ - futureErr d F φ = priceVar d F t φ := by
  unfold currentErr futureErr priceVar
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [← mul_sub, brier_sub_brier_self]

/-- Balance read at one coordinate: `∑_Q F Q · Q φ = t φ`.
Source: `bli-finite` `Balanced` (constraint 4)
Kind: L
Fidelity: exact -/
lemma balanced_sum_eq {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m}
    (hB : Balanced d F t) (φ : ↥(𝒮.S m)) :
    ∑ Q ∈ grid 𝒮 d (m + 1), F Q * Q (coord φ) = t φ :=
  hB φ

/-- **The accuracy gap** (X7-exact): for `F` a probability on the grid, balanced at `t`
(constraint 4), `currentErr F t φ − futureErr F φ = ∑_Q F Q · (Q φ)² − (t φ)²`. The step
`∑_Q F Q · Q φ = t φ` is `Balanced`, derived, not assumed.
Source: bli-paper-2-013 (b) ("`𝔼ₙ[ℙ_{f(n)}(φ)²] − ℙₙ(φ)²`"); mandate X7 (exact), judged item 5
Kind: P
Fidelity: exact (finite skeleton form; the LI form is `stretch`)
Hyps: (a) `IsProb d F`, `Balanced d F t` -/
theorem accuracy_gap {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m} (hF : IsProb d F)
    (hB : Balanced d F t) (φ : ↥(𝒮.S m)) :
    currentErr d F t φ - futureErr d F φ =
      ∑ Q ∈ grid 𝒮 d (m + 1), F Q * (Q (coord φ)) ^ 2 - (t φ) ^ 2 := by
  rw [accuracy_gap_eq_var]
  unfold priceVar
  have hsum : ∑ Q ∈ grid 𝒮 d (m + 1), F Q = 1 := hF.2.2
  have hbal := balanced_sum_eq hB φ
  have expand : ∀ Q : Table 𝒮 (m + 1), F Q * (Q (coord φ) - t φ) ^ 2 =
      F Q * (Q (coord φ)) ^ 2 - (2 * t φ) * (F Q * Q (coord φ)) + (t φ) ^ 2 * F Q := by
    intro Q; ring
  rw [Finset.sum_congr rfl fun Q _ => expand Q, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hbal, hsum]
  ring

/-- **Future accuracy is never worse** (Jensen on a finite sum): `futureErr ≤ currentErr`.
Source: bli-paper-2-013 (b); mandate X7 (exact)
Kind: P
Fidelity: exact
Hyps: (a) `IsProb d F` (nonnegativity of `F`) -/
theorem futureErr_le_currentErr {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} (hF : IsProb d F)
    (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) : futureErr d F φ ≤ currentErr d F t φ := by
  have h : 0 ≤ currentErr d F t φ - futureErr d F φ := by
    rw [accuracy_gap_eq_var]
    exact Finset.sum_nonneg fun Q _ => mul_nonneg (hF.1 Q) (sq_nonneg _)
  linarith

/-- **Equality iff the kernel is certain of its next price**: the gap vanishes iff `Q φ = t φ` on
every grid state of positive mass.
Source: bli-paper-2-013 (b) ("strictly better whenever the day-`n` market expects its price of
`φ` to move"); mandate X7 (exact)
Kind: P
Fidelity: exact
Hyps: (a) `IsProb d F` -/
theorem accuracy_gap_eq_zero_iff {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} (hF : IsProb d F)
    (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) :
    currentErr d F t φ = futureErr d F φ ↔
      ∀ Q ∈ grid 𝒮 d (m + 1), 0 < F Q → Q (coord φ) = t φ := by
  rw [← sub_eq_zero, accuracy_gap_eq_var]
  unfold priceVar
  rw [Finset.sum_eq_zero_iff_of_nonneg fun Q _ => mul_nonneg (hF.1 Q) (sq_nonneg _)]
  constructor
  · intro h Q hQ hpos
    have := h Q hQ
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (ne_of_gt hpos)
    · exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0)
  · intro h Q hQ
    rcases (hF.1 Q).lt_or_eq with hpos | hzero
    · rw [h Q hQ hpos, sub_self]; ring
    · rw [← hzero, zero_mul]

/-! ## Instances: the tent kernel (N+) and B0 (gap zero) -/

/-- A `{0,1}`-valued grid table over `t` that lies in the product face and reads `0` at a coordinate
where `t` is interior: `Q₀ ψ := 𝟙(t ψ = 1)` on old coordinates, `0` on new ones.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def lowFace (t : Table 𝒮 m) : Table 𝒮 (m + 1) :=
  fun ψ => if h : ψ.1 ∈ 𝒮.S m then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0) else 0

/-- `lowFace t` lies in the product face over `t` (a grid table agreeing with `t` wherever `t` is
`0` or `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lowFace_mem_faceProd (𝓜 : Mesh) (t : Table 𝒮 m) : lowFace t ∈ faceProd 𝒮 𝓜.d m t := by
  rw [mem_faceProd_iff, mem_grid_iff]
  refine ⟨fun ψ => ?_, fun φ hφ => ?_⟩
  · unfold lowFace
    split_ifs
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact zero_mem_gridVals _
    · exact zero_mem_gridVals _
  · rw [Table.restrict_apply]
    unfold lowFace
    rw [dif_pos φ.2]
    rcases hφ with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp

/-- `lowFace t` reads `0` at a coordinate where `t < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lowFace_coord (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) (h : t φ < 1) : lowFace t (coord φ) = 0 := by
  unfold lowFace coord
  rw [dif_pos φ.2, if_neg (ne_of_lt h)]

/-- **N+ — the tent kernel has a strictly positive gap at every interior coordinate**: for a unit
table `t` with `0 < t φ < 1`, the tent law `tentLaw 𝓜 m t` (a kernel: probability + balanced)
charges a state pricing `φ` at `0`, so `priceVar > 0` and `futureErr < currentErr`: the kernel is
uncertain of its own next price and expects to do strictly better by waiting.
Source: bli-paper-2-013 (b) (strict case); mandate X7 (N+: "`tentLaw_pos_iff`: two values charged")
Kind: N+
Fidelity: exact
Hyps: (a) `t.InUnit`, `0 < t φ < 1` -/
theorem tent_gap_pos (𝓜 : Mesh) {t : Table 𝒮 m} (ht : t.InUnit) (φ : ↥(𝒮.S m))
    (hφ0 : 0 < t φ) (hφ1 : t φ < 1) :
    IsProb 𝓜.d (tentLaw 𝓜 m t) ∧ Balanced 𝓜.d (tentLaw 𝓜 m t) t ∧
    0 < priceVar 𝓜.d (tentLaw 𝓜 m t) t φ ∧
      futureErr 𝓜.d (tentLaw 𝓜 m t) φ < currentErr 𝓜.d (tentLaw 𝓜 m t) t φ := by
  have hF : IsProb 𝓜.d (tentLaw 𝓜 m t) := tentLaw_isProb t
  have hB : Balanced 𝓜.d (tentLaw 𝓜 m t) t := tentLaw_balanced ht
  have hpos : 0 < tentLaw 𝓜 m t (lowFace t) :=
    (tentLaw_pos_iff ht (lowFace t)).2 (lowFace_mem_faceProd 𝓜 t)
  have hmem : lowFace t ∈ grid 𝒮 𝓜.d (m + 1) := faceProd_subset_grid 𝓜.d t (lowFace_mem_faceProd 𝓜 t)
  have hne : currentErr 𝓜.d (tentLaw 𝓜 m t) t φ ≠ futureErr 𝓜.d (tentLaw 𝓜 m t) φ := by
    intro heq
    have := (accuracy_gap_eq_zero_iff hF t φ).1 heq (lowFace t) hmem hpos
    rw [lowFace_coord t φ hφ1] at this
    linarith
  have hle := futureErr_le_currentErr hF t φ
  have hlt : futureErr 𝓜.d (tentLaw 𝓜 m t) φ < currentErr 𝓜.d (tentLaw 𝓜 m t) t φ :=
    lt_of_le_of_ne hle (Ne.symm hne)
  refine ⟨hF, hB, ?_, hlt⟩
  rw [← accuracy_gap_eq_var]
  linarith

/-- **B0 has gap zero**: the point-mass law `degLaw` at a grid table `t` prices every coordinate
exactly at `t` (nested grids), so `priceVar = 0` and `futureErr = currentErr`: "trust your prior"
holds exactly for the degenerate solution.
Source: bli-paper-2-013 (b) (degenerate case); mandate X7 ("B0's `pointMass` has gap `0`")
Kind: P
Fidelity: exact
Hyps: (a) `t ∈ grid 𝒮 𝓜.d m` (B0's standing hypothesis, `bli-trajectory` `b0_balance`) -/
theorem b0_gap_zero (𝓜 : Mesh) {t : Table 𝒮 m} (ht : t ∈ grid 𝒮 𝓜.d m) (φ : ↥(𝒮.S m)) :
    IsProb 𝓜.d (degLaw 𝓜.d m t) ∧ Balanced 𝓜.d (degLaw 𝓜.d m t) t ∧
    priceVar 𝓜.d (degLaw 𝓜.d m t) t φ = 0 ∧
      currentErr 𝓜.d (degLaw 𝓜.d m t) t φ = futureErr 𝓜.d (degLaw 𝓜.d m t) φ := by
  have hF : IsProb 𝓜.d (degLaw 𝓜.d m t) := pointMass_isProbOn (degStep_mem_grid 𝓜.d t)
  have hB : Balanced 𝓜.d (degLaw 𝓜.d m t) t := degLaw_balanced_of_mem_grid 𝓜 ht
  have hzero : priceVar 𝓜.d (degLaw 𝓜.d m t) t φ = 0 := by
    unfold priceVar degLaw
    simp only [pointMass_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' _ (degStep 𝓜.d m t), if_pos (degStep_mem_grid 𝓜.d t)]
    have : degStep 𝓜.d m t (coord φ) = t φ := by
      unfold coord
      rw [degStep_old]
      exact roundVal_eq_self (𝓜.d_pos _)
        (gridVals_mono (𝓜.d_dvd m) (𝓜.d_pos _) (mem_grid_iff.mp ht φ))
    rw [this, sub_self]; ring
  refine ⟨hF, hB, hzero, ?_⟩
  have := accuracy_gap_eq_var 𝓜.d (degLaw 𝓜.d m t) t φ
  rw [hzero] at this
  linarith

end Cleanroom.Bli.BliExactness
