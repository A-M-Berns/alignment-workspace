import Cleanroom.Decision.DpWorldsJb.Expressivity

/-!
# The CDT-foundations literature check (T10): Gallow's coincidence over a finite algebra

Source: a Deep-Research report reproduced in the CDT-foundations chat
(`research/decision-problems/chats/2026-07-04__causal-decision-theory-foundations__6a5ccc81.md`
lines 264–280), summarizing Gallow 2024 (*PPQ* 105(1)); the paper is not in the repo, so the
evaluators below are **(b)** and ATTRIBUTION-UNVETTED, and no proposition numbers are cited.

Finite atomic carrier `Finset Ω`, `V : Ω → ℝ` on atoms, `P : Dist Ω`:
* `U₃ PA V := ∑_ω PA ω · V ω` (Sobel/Joyce: a supposition `PA` with `PA A = 1` — v2's causal
  evaluator under rigidity, T3);
* `U₂ P V A k := ∑_c P (K_c) · E_P[V | A ⊓ K_c]` over the dependency-hypothesis partition
  `K_c := k⁻¹{c}` (Lewis/Skyrms; Lean-total division, so `P (A ⊓ K_c) = 0` terms vanish — a
  convention the report does not make, disclosed as `(c)`);
* `U₁ P V A k sel := ∑_c P (K_c) · V (sel c)` (Gibbard–Harper, the determinate special case
  where every `A ⊓ K_c` is the atom `sel c`).

`gallow_U2_eq_U3_of_imaging`: `U₂ = U₃` when `PA` is `K`-imaging,
`PA ω := P (K_{k ω}) · P ω / P (A ⊓ K_{k ω})` on `ω ∈ A`; `gallow_U1_eq_U2_of_determinate`:
`U₁ = U₂` under determinacy with charged selected atoms. Both are regroupings that hold by
construction of the definitions (kind L). `imaging` is a supposition (`PA A = 1`) exactly when
every charged dependency hypothesis meets `A` with positive probability
(`imaging_sum_eq_one`, `mass_imaging_eq_one`); otherwise it is a sub-probability and `U₂`
silently drops the uncharged cells (`imaging_sum_lt_one_example`, audit r1 N2/N3).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype κ] [DecidableEq κ]

/-- The dependency hypothesis `K_c := {ω | k ω = c}` of a labeling `k`.
Source: CDT-foundations chat lines 264–280 (Lewis's dependency hypotheses / Skyrms's `K`-partition) | dp-core-2-054(b)
Kind: D
Fidelity: exact (a partition given as a labeling)
Hyps: n/a -/
def depH (k : Ω → κ) (c : κ) : Finset Ω := univ.filter (fun ω => k ω = c)

theorem mem_depH (k : Ω → κ) (c : κ) (ω : Ω) : ω ∈ depH k c ↔ k ω = c := by simp [depH]

/-- Sobel/Joyce: `U₃ A := ∑_ω P^A ω · V ω` for a supposition `P^A`.
Source: CDT-foundations chat line 272 ("`U₃(A) = Σ_W P^A(W)·V(W)`") | dp-core-2-054(b)
Kind: D
Fidelity: exact; (b) taken from a secondary report of Gallow 2024, ATTRIBUTION-UNVETTED
Hyps: n/a -/
def U₃ (PA V : Ω → ℝ) : ℝ := ∑ ω, PA ω * V ω

/-- Lewis/Skyrms: `U₂ A := ∑_c P (K_c) · E_P[V | A ⊓ K_c]` (multiplicative-safe: a term with
`P (A ⊓ K_c) = 0` vanishes by Lean's `x / 0 = 0` — a convention the report does not make).
Source: CDT-foundations chat line 270 ("`U₂(A) = Σ_K P(K)·V(AK)`") | dp-core-2-054(b)
Kind: D
Fidelity: exact up to the null-term convention; (b), ATTRIBUTION-UNVETTED
Hyps: (c) the `0 / 0 = 0` convention for null `A ⊓ K_c` -/
def U₂ (P V : Ω → ℝ) (A : Finset Ω) (k : Ω → κ) : ℝ :=
  ∑ c, mass P (depH k c) * condExp P V (A ∩ depH k c)

/-- Gibbard–Harper, rendered as the determinate special case: `U₁ A := ∑_c P (K_c) · V (sel c)`
when `A ⊓ K_c` is the single atom `sel c`.
Source: CDT-foundations chat line 268 ("`U₁(A) = Σ_O P(A □→ O)·V(O)`") | dp-core-2-054(b)
Kind: D
Fidelity: variant: the determinate special case; (b), ATTRIBUTION-UNVETTED
Hyps: n/a -/
def U₁ (P V : Ω → ℝ) (k : Ω → κ) (sel : κ → Ω) : ℝ :=
  ∑ c, mass P (depH k c) * V (sel c)

/-- `K`-imaging: `P^A ω := P (K_{k ω}) · P ω / P (A ⊓ K_{k ω})` on `ω ∈ A`, `0` off `A`.
Source: CDT-foundations chat lines 264–280 (Lewis's imaging within dependency hypotheses) | dp-core-2-054(b)
Kind: D
Fidelity: exact; (b), ATTRIBUTION-UNVETTED
Hyps: n/a -/
def imaging (P : Ω → ℝ) (A : Finset Ω) (k : Ω → κ) : Ω → ℝ := fun ω =>
  if ω ∈ A then mass P (depH k (k ω)) * P ω / mass P (A ∩ depH k (k ω)) else 0

/-- **T10.** `U₂ = U₃` when the supposition is `K`-imaging: regroup `∑_{ω ∈ A}` by the value
of `k`. This holds for every `P`, `A`, `k` because `imaging` is defined as the reweighting that
makes it hold (a `Finset.sum_fiberwise` regrouping); `imaging` is a genuine supposition only
under the charged-cells hypothesis of `mass_imaging_eq_one`.
Source: CDT-foundations chat line 276 ("`U₃` is a generalisation of `U₂`", coincidence under the added assumption) | dp-core-2-054(b)
Kind: L
Fidelity: exact for the definitions above; (b) the evaluators are from a secondary report,
ATTRIBUTION-UNVETTED; (c) null-term convention
Hyps: (b) the three evaluators as stated in the report; (c) `0 / 0 = 0` in `U₂` and `imaging` -/
theorem gallow_U2_eq_U3_of_imaging (P V : Ω → ℝ) (A : Finset Ω) (k : Ω → κ) :
    U₂ P V A k = U₃ (imaging P A k) V := by
  unfold U₃ U₂ imaging
  rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ A)]
  have h2 : ∑ ω ∈ univ.filter (fun ω => ω ∉ A),
      (if ω ∈ A then mass P (depH k (k ω)) * P ω / mass P (A ∩ depH k (k ω)) else 0) * V ω = 0 := by
    apply sum_eq_zero
    intro ω hω
    rw [mem_filter] at hω
    rw [if_neg hω.2, zero_mul]
  rw [h2, add_zero]
  have hA : univ.filter (fun ω => ω ∈ A) = A := by
    ext ω
    simp
  rw [hA]
  rw [← sum_fiberwise A k]
  apply sum_congr rfl
  intro c _
  have hf : A.filter (fun ω => k ω = c) = A ∩ depH k c := by
    ext ω
    simp [depH]
  unfold condExp
  have hterm : ∀ i ∈ A.filter (fun ω => k ω = c),
      (if i ∈ A then mass P (depH k (k i)) * P i / mass P (A ∩ depH k (k i)) else 0) * V i =
        mass P (depH k c) * (P i * V i) * (mass P (A ∩ depH k c))⁻¹ := by
    intro i hi
    rw [mem_filter] at hi
    rw [if_pos hi.1, hi.2, div_eq_mul_inv]
    ring
  rw [sum_congr rfl hterm, ← sum_mul, ← mul_sum, hf, div_eq_mul_inv]
  ring

/-- **T10, determinate case.** `U₁ = U₂` when every `A ⊓ K_c` is the single charged atom
`sel c` (a conditional expectation over a charged singleton is the value there).
Source: CDT-foundations chat line 276 ("`U₂` was a generalisation of `U₁`") | dp-core-2-054(b)
Kind: L
Fidelity: exact for the definitions above; (b) ATTRIBUTION-UNVETTED
Hyps: (b) the evaluators as stated; (a) determinacy and charging are hypotheses -/
theorem gallow_U1_eq_U2_of_determinate (P V : Ω → ℝ) (A : Finset Ω) (k : Ω → κ) (sel : κ → Ω)
    (hdet : ∀ c, A ∩ depH k c = {sel c}) (hpos : ∀ c, 0 < P (sel c)) :
    U₁ P V k sel = U₂ P V A k := by
  unfold U₁ U₂
  apply sum_congr rfl
  intro c _
  rw [hdet c, condExp_singleton (hpos c)]

/-- v2's causal evaluator (Definition 17's shape, `V^a_s a` with a *supposed* value function)
under rigidity is `U₃` with the actual atom values: the supposed desirability of `a` for the
rigid pair is `∑_ω P^a ω · V_s{ω} / P^a a`, i.e. `U₃ (P^a) (V_s{·})` when `P^a a = 1`.
Source: [[decision-problems-v2]] Definition 17 (CDT); CDT-foundations chat line 272 | dp-core-2-054(b)
Kind: L
Fidelity: exact (finite atomic carrier)
Hyps: n/a -/
theorem rigid_supposedValue_eq_U₃ {W : Type*} [Fintype W] [DecidableEq W] (π : W → Ω)
    (μ μa : Dist W) (u : W → ℝ) (a : Finset Ω) (ha : mass (push π μa.p) a = 1) :
    rigidV π μ.p μa.p u a = U₃ (push π μa.p) (fun ω => coarseV π μ.p u {ω}) := by
  have hsupp : ∀ ω, ω ∉ a → push π μa.p ω = 0 := by
    intro ω hω
    have htot : mass (push π μa.p) univ = 1 := (μa.pushforward π).sum_one
    have hsplit : mass (push π μa.p) univ = mass (push π μa.p) a + mass (push π μa.p) aᶜ := by
      rw [← mass_union _ disjoint_compl_right, union_compl]
    have hc : mass (push π μa.p) aᶜ = 0 := by linarith
    exact (mass_eq_zero_iff (push_nonneg π μa.nonneg) aᶜ).1 hc ω (mem_compl.2 hω)
  unfold rigidV condExp U₃
  rw [ha, div_one]
  rw [← sum_subset (subset_univ a)]
  intro ω _ hω
  rw [hsupp ω hω, zero_mul]

/-! ### When is `imaging` a supposition? (audit r1, N2/N3) -/

/-- The dependency hypotheses partition the mass: `∑_c P (K_c) = ∑_ω P ω`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem sum_mass_depH (P : Ω → ℝ) (k : Ω → κ) : ∑ c, mass P (depH k c) = ∑ ω, P ω := by
  unfold mass depH
  exact sum_fiberwise univ k P

/-- `imaging P A k` sums to `1` when `P` is a probability and every charged dependency
hypothesis meets `A` with positive probability: each charged cell `A ⊓ K_c` receives the whole
mass `P (K_c)`, and an uncharged `K_c` has `P (K_c) = 0`.
Source: CDT-foundations chat lines 264–280 (imaging as a supposition `P^A`) | dp-core-2-054(b)
Kind: L
Fidelity: exact
Hyps: (a) the charged-cells hypothesis is what makes imaging a probability; without it the
example `imaging_sum_lt_one_example` sums to `1/2` -/
theorem imaging_sum_eq_one (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1)
    (A : Finset Ω) (k : Ω → κ)
    (hcell : ∀ c, 0 < mass P (depH k c) → 0 < mass P (A ∩ depH k c)) :
    ∑ ω, imaging P A k ω = 1 := by
  have hA : ∑ ω, imaging P A k ω =
      ∑ ω ∈ A, mass P (depH k (k ω)) * P ω / mass P (A ∩ depH k (k ω)) := by
    unfold imaging
    rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ A)]
    have h2 : ∑ ω ∈ univ.filter (fun ω => ω ∉ A),
        (if ω ∈ A then mass P (depH k (k ω)) * P ω / mass P (A ∩ depH k (k ω)) else 0) = 0 := by
      apply sum_eq_zero
      intro ω hω
      rw [mem_filter] at hω
      rw [if_neg hω.2]
    rw [h2, add_zero]
    have hA' : univ.filter (fun ω => ω ∈ A) = A := by
      ext ω
      simp
    rw [hA']
    apply sum_congr rfl
    intro ω hω
    rw [if_pos hω]
  rw [hA, ← sum_fiberwise A k, ← hsum, ← sum_mass_depH P k]
  apply sum_congr rfl
  intro c _
  have hf : A.filter (fun ω => k ω = c) = A ∩ depH k c := by
    ext ω
    simp [depH]
  have hterm : ∀ ω ∈ A.filter (fun ω => k ω = c),
      mass P (depH k (k ω)) * P ω / mass P (A ∩ depH k (k ω)) =
        mass P (depH k c) / mass P (A ∩ depH k c) * P ω := by
    intro ω hω
    rw [mem_filter] at hω
    rw [hω.2, div_mul_eq_mul_div]
  rw [sum_congr rfl hterm, ← mul_sum, hf]
  change mass P (depH k c) / mass P (A ∩ depH k c) * mass P (A ∩ depH k c) = mass P (depH k c)
  by_cases hpos : 0 < mass P (A ∩ depH k c)
  · exact div_mul_cancel₀ _ hpos.ne'
  · have h0 : mass P (A ∩ depH k c) = 0 := le_antisymm (not_lt.1 hpos) (mass_nonneg hP _)
    have hK : mass P (depH k c) = 0 := by
      by_contra hne
      exact hpos (hcell c (lt_of_le_of_ne (mass_nonneg hP _) (Ne.symm hne)))
    rw [h0, hK]
    simp

/-- Under the same hypotheses `imaging` is a **supposition** in v2's sense: its mass on `A` is
`1` (it vanishes off `A`).
Source: CDT-foundations chat line 272 (`U₃` "for a supposition `P^A`"); [[decision-problems-v2]] Definition 2 (success `P^a(a) = 1`) | dp-core-2-054(b)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mass_imaging_eq_one (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1)
    (A : Finset Ω) (k : Ω → κ)
    (hcell : ∀ c, 0 < mass P (depH k c) → 0 < mass P (A ∩ depH k c)) :
    mass (imaging P A k) A = 1 := by
  rw [← imaging_sum_eq_one P hP hsum A k hcell]
  unfold mass
  apply sum_subset (subset_univ A)
  intro ω _ hω
  unfold imaging
  rw [if_neg hω]

/-- `depH id c = {c}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem depH_id (c : Ω) : depH (id : Ω → Ω) c = {c} := by
  ext ω
  simp [mem_depH]

/-- The uniform distribution on `Bool`.
Source: none: infrastructure (audit r1 probes)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def uniformBool : Bool → ℝ := fun _ => 1 / 2

/-- **Without the charged-cells hypothesis `imaging` is not a supposition**: with `Ω = κ = Bool`,
`k = id`, `A = {true}` and `P` uniform, the dependency hypothesis `K_false` (mass `1/2`) misses
`A`, and the imaging mass is `1/2`, not `1` — the cell is silently dropped by the `0/0 = 0`
convention (`(c)` in `U₂` and `imaging`).
Source: none: infrastructure (audit r1 probes)
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem imaging_sum_lt_one_example :
    ∑ ω, imaging uniformBool ({true} : Finset Bool) (id : Bool → Bool) ω = 1 / 2 := by
  rw [Fintype.sum_bool]
  unfold imaging
  rw [if_pos (by simp), if_neg (by simp)]
  simp only [id, depH_id]
  unfold mass
  simp [uniformBool]

end

end Cleanroom.Decision.DpWorldsJb
