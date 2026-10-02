import Cleanroom.Lit.LitShutdownPrefs.TimestepDominance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Appendix C.4: an ILPACS violation makes the policy dominated (Target 11)

The paper's model: the agent faces, with probabilities `r, s ∈ (0,1)` (`r + s < 1`, the rest
covered by a catch-all `Z`), the free choice among `X₁, …, Xₙ` — where Maximality makes it choose
stochastically with probabilities `a i > 0` — and the choice `{X, Y}` — where, ILPACS being
violated (`¬ X ≻ Y`), it chooses `X` with probability `b < 1`. The induced mass function is
`induced = r ∑ aᵢ Xᵢ + s (b X + (1−b) Y) + (1−r−s) Z`.

`DominatedRep lt Xs Ys L L'` is the paper's "Dominated Policy" (l. 318 ff.): `L` is
`∑ cᵢ (dᵢ Xᵢ + (1−dᵢ) Yᵢ) + Z'` and `L'` is `∑ cᵢ ((dᵢ+eᵢ) Xᵢ + (1−dᵢ−eᵢ) Yᵢ) + Z'` with
`cᵢ ∈ (0,1)`, `dᵢ ∈ [0,1]`, `eᵢ > 0`, `dᵢ + eᵢ ≤ 1`, `Z' ≥ 0` (so that both displays are mixtures
of lotteries — audit round 1, adversarial N1: without the last three clauses the zero mass function
was "dominated" by a signed measure), `Xᵢ ≽ Yᵢ` for all `i` and `Xᵢ ≻ Yᵢ` for some.

`dominated_of_ilpacs_violation`: the policy `(a + ε, b + δ)` with `εᵢ = s δ (qᵢ − pᵢ)/r` dominates
`(a, b)`, for any `δ > 0` keeping `a + ε` positive and `b + δ ≤ 1`, with
`cᵢ = r aᵢ + s b pᵢ + s(1−b) qᵢ`, `dᵢ = (r aᵢ + s b pᵢ)/cᵢ`, `eᵢ = s δ qᵢ / cᵢ` — the paper's
computation. (Presentation note on the source: the paper defines `eᵢ = Pr_π′{Xᵢ} − Pr_π{Xᵢ}`, an
absolute increment, and then uses it as the within-`cᵢ` share; the share `s δ qᵢ / cᵢ` is what the
displayed representation needs.) `exists_delta` supplies such a `δ` for every admissible data
(`δ = min (1 − b) (r ∏ aᵢ / 2s)`), and `dominated_of_ilpacs_violation_exists` packages the two.
`dominated_full_witness` inhabits the theorem's *full* hypothesis package — relation, lotteries,
ILPACS antecedents, environment, policy, `δ` — with the `not_ilpacs_TD` data (audit round 1,
adversarial B2: the previous witness inhabited only the arithmetic side conditions).

**(c)**: the environment offers the two situations with `r, s > 0`, `r + s < 1`; the policy's
probabilities `a` (all positive, summing to one) and `b < 1` are what Maximality dictates for
the ILPACS-violating agent (the paper's steps 1–2) and are taken as given.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Dominated

open Lottery Strict Finset

variable {n : ℕ}

/-- The mass function induced by the policy `(a, b)` in the two-situation environment.
Source: DReST App. C.4 (l. 318: the lottery induced by `π`)
Kind: D
Fidelity: exact -/
noncomputable def induced (r s : ℝ) (X Y : Lottery Traj) (Xs : Fin n → Lottery Traj) (Z : Lottery Traj)
    (a : Fin n → ℝ) (b : ℝ) : Traj →₀ ℝ :=
  r • ∑ i, a i • (Xs i).p + s • (b • X.p + (1 - b) • Y.p) + (1 - r - s) • Z.p

/-- **Dominated Policy** (the paper's definition): `L` and `L'` are the mass functions of two
policies of the displayed forms, with `cᵢ ∈ (0,1)`, `dᵢ ∈ [0,1]`, `eᵢ > 0`, `dᵢ + eᵢ ≤ 1`, a
nonnegative remainder `Z'`, and `Xᵢ ≽ Yᵢ` for all `i`, `Xᵢ ≻ Yᵢ` for some `i`. The well-formedness
clauses (`dᵢ ∈ [0,1]`, `dᵢ + eᵢ ≤ 1`, `Z' ≥ 0`) make the displays genuine mixtures of lotteries;
the paper leaves them implicit.
Source: DReST App. C.4 l. 318 ff. (Dominated Policy)
Kind: D
Fidelity: exact (well-formedness of the decomposition made explicit) -/
def DominatedRep (lt : Lottery Traj → Lottery Traj → Prop) (Xs Ys : Fin n → Lottery Traj)
    (L L' : Traj →₀ ℝ) : Prop :=
  (∀ i, le lt (Xs i) (Ys i)) ∧ (∃ i, lt (Xs i) (Ys i)) ∧
    ∃ (c d e : Fin n → ℝ) (Z' : Traj →₀ ℝ), (∀ i, c i ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, 0 < e i) ∧ (∀ i, d i + e i ≤ 1) ∧ (∀ t, 0 ≤ Z' t) ∧
      L = ∑ i, c i • (d i • (Xs i).p + (1 - d i) • (Ys i).p) + Z' ∧
      L' = ∑ i, c i • ((d i + e i) • (Xs i).p + (1 - d i - e i) • (Ys i).p) + Z'

/-- The perturbed free-choice probabilities `aᵢ + s δ (qᵢ − pᵢ)/r`.
Source: DReST App. C.4 (`ϵᵢ = s δ (qᵢ − pᵢ)/r`)
Kind: D -/
noncomputable def perturbed (r s δ : ℝ) (p q a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a i + s * δ * (q i - p i) / r

/-- The perturbed probabilities still sum to one.
Source: DReST App. C.4 ("It's also necessary that `∑ ϵᵢ = 0`. That follows from `∑ pᵢ = 1` and `∑ qᵢ = 1`")
Kind: L -/
theorem sum_perturbed (r s δ : ℝ) (_hr : r ≠ 0) (p q a : Fin n → ℝ) (hp : ∑ i, p i = 1)
    (hq : ∑ i, q i = 1) (ha : ∑ i, a i = 1) : ∑ i, perturbed r s δ p q a i = 1 := by
  unfold perturbed
  rw [Finset.sum_add_distrib, ha]
  have : ∑ i, s * δ * (q i - p i) / r = (s * δ / r) * (∑ i, q i - ∑ i, p i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, hq, hp]
  simp

/-- **A small enough `δ` always exists**: `δ = min (1 − b) (r ∏ aᵢ / 2s)` is positive, keeps
`b + δ ≤ 1`, and keeps every perturbed probability positive (since `∏ aⱼ ≤ aᵢ` and `|qᵢ − pᵢ| < 1`).
Source: DReST App. C.4 ("for small enough `δ`"); audit round 1, fidelity non-blocking 6
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem exists_delta (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (p q a : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) (hq : ∀ i, q i ∈ Set.Ioo (0 : ℝ) 1)
    (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (b : ℝ) (hb1 : b < 1) :
    ∃ δ : ℝ, 0 < δ ∧ b + δ ≤ 1 ∧ ∀ i, 0 < perturbed r s δ p q a i := by
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have ha_le : ∀ i, a i ≤ 1 := fun i => by
    have := Finset.single_le_sum (f := a) (fun j _ => (ha j).le) (Finset.mem_univ i)
    linarith
  have hprod_le : ∀ i, ∏ j, a j ≤ a i := fun i => by
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact mul_le_of_le_one_right (ha i).le
      (Finset.prod_le_one (fun j _ => (ha j).le) (fun j _ => ha_le j))
  have hpos : 0 < r * (∏ i, a i) / (2 * s) := div_pos (mul_pos hr hprod) (by positivity)
  refine ⟨min (1 - b) (r * (∏ i, a i) / (2 * s)), lt_min (by linarith) hpos, ?_, fun i => ?_⟩
  · have := min_le_left (1 - b) (r * (∏ i, a i) / (2 * s)); linarith
  · unfold perturbed
    have hδ := min_le_right (1 - b) (r * (∏ i, a i) / (2 * s))
    have hδ0 : 0 < min (1 - b) (r * (∏ i, a i) / (2 * s)) := lt_min (by linarith) hpos
    set δ := min (1 - b) (r * (∏ i, a i) / (2 * s)) with hδdef
    have h1 : s * δ / r ≤ a i / 2 := by
      rw [div_le_iff₀ hr]
      have h2 : s * δ ≤ s * (r * (∏ i, a i) / (2 * s)) := mul_le_mul_of_nonneg_left hδ hs.le
      have h3 : s * (r * (∏ i, a i) / (2 * s)) = r * (∏ i, a i) / 2 := by field_simp
      have h4 : r * (∏ i, a i) / 2 ≤ a i / 2 * r := by nlinarith [hprod_le i, hr]
      linarith
    have h2 : (0 : ℝ) < q i - p i + 1 := by have := (hq i).1; have := (hp i).2; linarith
    have h3 : 0 < s * δ / r := by positivity
    have h4 : s * δ * (q i - p i) / r = (s * δ / r) * (q i - p i) := by ring
    rw [h4]
    nlinarith [mul_pos h3 h2, ha i]

/-- **An ILPACS-violating policy is dominated** (DReST App. C.4). Given the ILPACS data
(`X = ∑ pᵢ Xᵢ`, `Y = ∑ qᵢ Yᵢ`, `pᵢ, qᵢ ∈ (0,1)`, `Xᵢ ≽ Yᵢ` all `i`, `Xᵢ ≻ Yᵢ` some `i`), the environment
(`r, s > 0`, `r + s < 1`, catch-all `Z`) and the policy (`aᵢ > 0`, `∑ aᵢ = 1`, `0 ≤ b < 1`), for any
`δ > 0` with `b + δ ≤ 1` and `aᵢ + s δ (qᵢ − pᵢ)/r > 0`, the policy `(a + ε, b + δ)` is available
(its probabilities sum to one) and its induced mass function dominates that of `(a, b)`.
Source: DReST App. C.4 ll. 296–330 (the proof that `π'` dominates `π`); corr-refs-2-017;
[[lit-shutdown-prefs-mandate]] Target 11
Kind: P
Fidelity: exact (of the paper's computation; the pairwise lack of preference among the `Xᵢ` enters
only through Maximality's `aᵢ > 0`, taken as given)
Hyps: (a) the ILPACS antecedents and the arithmetic; (c) the two-situation environment with `r, s > 0`,
`r + s < 1`, and the Maximality-dictated policy probabilities `aᵢ > 0`, `b < 1` taken as given -/
theorem dominated_of_ilpacs_violation (lt : Lottery Traj → Lottery Traj → Prop) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s < 1) (p q : Fin n → ℝ) (Xs Ys : Fin n → Lottery Traj)
    (X Y : Lottery Traj) (hX : X.p = ∑ i, p i • (Xs i).p) (hY : Y.p = ∑ i, q i • (Ys i).p)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) (hq : ∀ i, q i ∈ Set.Ioo (0 : ℝ) 1)
    (hle : ∀ i, le lt (Xs i) (Ys i)) (hlt : ∃ i, lt (Xs i) (Ys i)) (Z : Lottery Traj)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (δ : ℝ) (hδ : 0 < δ) (hbδ : b + δ ≤ 1) (_haδ : ∀ i, 0 < perturbed r s δ p q a i) :
    (∑ i, perturbed r s δ p q a i = 1) ∧
      DominatedRep lt Xs Ys (induced r s X Y Xs Z a b)
        (induced r s X Y Xs Z (perturbed r s δ p q a) (b + δ)) := by
  have hp1 : ∑ i, p i = 1 := by
    have h := congrArg (fun f : Traj →₀ ℝ => ∑ t ∈ f.support, f t) hX
    rw [X.sum_one, ← wsum_one, wsum_finset_sum] at h
    simp only [wsum_smul] at h
    simp only [wsum_one, (Xs _).sum_one, mul_one] at h
    exact h.symm
  have hq1 : ∑ i, q i = 1 := by
    have h := congrArg (fun f : Traj →₀ ℝ => ∑ t ∈ f.support, f t) hY
    rw [Y.sum_one, ← wsum_one, wsum_finset_sum] at h
    simp only [wsum_smul] at h
    simp only [wsum_one, (Ys _).sum_one, mul_one] at h
    exact h.symm
  refine ⟨sum_perturbed r s δ hr.ne' p q a hp1 hq1 ha1, hle, hlt, ?_⟩
  -- the paper's cᵢ, dᵢ, eᵢ
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ i, c i = r * a i + s * b * p i + s * (1 - b) * q i :=
    ⟨_, fun i => rfl⟩
  have hcpos : ∀ i, 0 < c i := fun i => by
    rw [hc]
    have := ha i; have := (hp i).1; have := (hq i).1
    have h1 : 0 ≤ s * b * p i := by positivity
    have h2 : 0 ≤ s * (1 - b) * q i := mul_nonneg (mul_nonneg hs.le (by linarith)) (hq i).1.le
    nlinarith
  have ha_le : ∀ i, a i ≤ 1 := fun i => by
    have := Finset.single_le_sum (f := a) (fun j _ => (ha j).le) (Finset.mem_univ i)
    linarith
  have hclt : ∀ i, c i < 1 := fun i => by
    rw [hc]
    have h1 : r * a i ≤ r := mul_le_of_le_one_right hr.le (ha_le i)
    have h2 : s * b * p i ≤ s * b := mul_le_of_le_one_right (mul_nonneg hs.le hb0) (hp i).2.le
    have h3 : s * (1 - b) * q i ≤ s * (1 - b) :=
      mul_le_of_le_one_right (mul_nonneg hs.le (by linarith)) (hq i).2.le
    nlinarith
  have hr' : r ≠ 0 := hr.ne'
  have hnum_nonneg : ∀ i, 0 ≤ r * a i + s * b * p i := fun i => by
    have := ha i; have := (hp i).1; positivity
  have hnum_le : ∀ i, r * a i + s * b * p i ≤ c i := fun i => by
    rw [hc]
    have : 0 ≤ s * (1 - b) * q i := mul_nonneg (mul_nonneg hs.le (by linarith)) (hq i).1.le
    linarith
  refine ⟨c, fun i => (r * a i + s * b * p i) / c i, fun i => s * δ * q i / c i, (1 - r - s) • Z.p,
    fun i => ⟨hcpos i, hclt i⟩, fun i => ⟨div_nonneg (hnum_nonneg i) (hcpos i).le,
      (div_le_one (hcpos i)).mpr (hnum_le i)⟩,
    fun i => by have := hcpos i; have := (hq i).1; positivity, fun i => ?_, fun t => ?_, ?_, ?_⟩
  · -- dᵢ + eᵢ ≤ 1 ⟺ s δ qᵢ ≤ s (1 − b) qᵢ ⟸ δ ≤ 1 − b
    rw [← add_div, div_le_one (hcpos i), hc]
    have h1 : s * δ * q i ≤ s * (1 - b) * q i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hs.le) (hq i).1.le
    linarith
  · -- the remainder is nonnegative
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (Z.nonneg t)
  · -- the representation of π
    ext t
    simp only [induced, hX, hY, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply,
      smul_eq_mul, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci := (hcpos i).ne'
    field_simp
    rw [hc]
    ring
  · -- the representation of π'
    ext t
    simp only [induced, hX, hY, perturbed, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.finsetSum_apply, smul_eq_mul, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci := (hcpos i).ne'
    field_simp
    rw [hc]
    ring

/-- **App. C.4 with the `δ` supplied**: for every ILPACS-violating datum and every admissible
environment and policy, some `(a + ε, b + δ)` is available and dominates `(a, b)`.
Source: DReST App. C.4 (the theorem as the paper states it, "for small enough `δ`")
Kind: C
Fidelity: exact
Hyps: (a) the ILPACS antecedents; (c) as in `dominated_of_ilpacs_violation` -/
theorem dominated_of_ilpacs_violation_exists (lt : Lottery Traj → Lottery Traj → Prop) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s < 1) (p q : Fin n → ℝ) (Xs Ys : Fin n → Lottery Traj)
    (X Y : Lottery Traj) (hX : X.p = ∑ i, p i • (Xs i).p) (hY : Y.p = ∑ i, q i • (Ys i).p)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) (hq : ∀ i, q i ∈ Set.Ioo (0 : ℝ) 1)
    (hle : ∀ i, le lt (Xs i) (Ys i)) (hlt : ∃ i, lt (Xs i) (Ys i)) (Z : Lottery Traj)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ δ : ℝ, 0 < δ ∧ b + δ ≤ 1 ∧ (∀ i, 0 < perturbed r s δ p q a i) ∧
      (∑ i, perturbed r s δ p q a i = 1) ∧
      DominatedRep lt Xs Ys (induced r s X Y Xs Z a b)
        (induced r s X Y Xs Z (perturbed r s δ p q a) (b + δ)) := by
  obtain ⟨δ, hδ, hbδ, haδ⟩ := exists_delta r s hr hs p q a hp hq ha ha1 b hb1
  exact ⟨δ, hδ, hbδ, haδ, dominated_of_ilpacs_violation lt r s hr hs hrs p q Xs Ys X Y hX hY hp hq
    hle hlt Z a ha ha1 b hb0 hb1 δ hδ hbδ haδ⟩

/-- **The full hypothesis package is inhabited** by the `not_ilpacs_TD` data: `lt :=
TimestepDominates`, `Xs = (X₁, X₂)`, `Ys = (X₁, Y₂)` with `X₂ ≻_TD Y₂` (`TD_ilX₂_ilY₂`) and
`X₁ ~ X₁`, `X = 0.9X₁ + 0.1X₂`, `Y = 0.1X₁ + 0.9Y₂`, `r = s = 1/4`, `Z = [ ]`, `a = (½, ½)`,
`b = ½`, `δ = 1/10` (perturbed probabilities `(0.42, 0.58)`, `b + δ = 0.6`). Relation, lotteries,
ILPACS antecedents, environment, policy and `δ` are all supplied; the conclusion is then the
theorem's.
Source: [[lit-shutdown-prefs-mandate]] Target 11 (witness); audit round 1, adversarial B2
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem dominated_full_witness :
    (∑ i, perturbed (1/4) (1/4) (1/10) ![9/10, 1/10] ![1/10, 9/10] ![1/2, 1/2] i = 1) ∧
      DominatedRep TimestepDominates ![ilX₁, ilX₂] ![ilX₁, ilY₂]
        (induced (1/4) (1/4) ilX ilY ![ilX₁, ilX₂] (dirac []) ![1/2, 1/2] (1/2))
        (induced (1/4) (1/4) ilX ilY ![ilX₁, ilX₂] (dirac [])
          (perturbed (1/4) (1/4) (1/10) ![9/10, 1/10] ![1/10, 9/10] ![1/2, 1/2]) (1/2 + 1/10)) :=
  dominated_of_ilpacs_violation TimestepDominates (1/4) (1/4) (by norm_num) (by norm_num)
    (by norm_num) ![9/10, 1/10] ![1/10, 9/10] ![ilX₁, ilX₂] ![ilX₁, ilY₂] ilX ilY rfl rfl
    (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
    (fun i => by
      fin_cases i
      · exact Or.inr (Strict.indiff_self _ (TD_irrefl _))
      · exact Or.inl TD_ilX₂_ilY₂)
    ⟨1, TD_ilX₂_ilY₂⟩ (dirac []) ![1/2, 1/2] (fun i => by fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) (1/2) (by norm_num) (by norm_num) (1/10) (by norm_num)
    (by norm_num) (fun i => by fin_cases i <;> norm_num [perturbed])

end Dominated

end Cleanroom.Lit.LitShutdownPrefs
