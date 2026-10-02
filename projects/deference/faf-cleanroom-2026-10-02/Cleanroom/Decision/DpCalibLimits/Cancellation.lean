import Cleanroom.Decision.DpCalibLimits.Popper

/-!
# T6(b), T7(a)–(c) — The cancellation lemma, the manifold's factorisation, self-transparency
on it, and which zeros survive

[[dp-calib-limits-mandate]] T6(b) (dp-cf-2-042, "not adversarially re-reviewed" — proved
here), T7(a)–(c) (dp-cf-045, CA-8′, v2 Q2, Remark 3.7).

* **The factorisation** (`sum_leafLaw_deviate_eq`): at a point met at most once per run and
  covered (for the uniform deviation), every `O_d`-leaf with positive off-`d` weight passes
  exactly one `d`-node, so under `C[d ↦ m]` its law is `m(a) · offWeight_C(ℓ)` for the edge
  `a` it takes, and `ν_{C[d↦m]}(X ∩ O_d) = ∑_a m(a) θ_a(X ∩ O_d)` with `θ_a` `m`-free
  (`nu_deviate_eq`, `paySum_deviate_eq`). This is CA-8′'s ratio formula: `M_d` is the image of
  the open simplex under an `m`-affine map divided by an `m`-affine normaliser.
* **The cancellation lemma** (`cancellation`, `condExp_deviate_eq`): with every `d`-node
  action-veridical and disjoint action events, only the `a`-term survives on the `a`-event,
  and `m(a)` cancels — masked act values are self-model-free, so masked and limit EDT
  verdicts can differ at most through `A_d^+`. Necessity of `¬ Nested`: `Zo1.lean`.
* **The manifold** (`maskedClause1_iff_mem_manifold`): membership is masked clause 1.
* **Self-transparency on the manifold** (`nu_deviate_actEv_eq_self`): with every `d`-node
  subtree- and action-veridical, `P(a | O_d) = m(a)` — derived from
  `nu_actEv_inter_obs_of_recordsFor` after proving recording from the veridicality package
  (`recordsFor_of_veridical`).
* **Which zeros survive** (`zero_survives_iff`, Remark 3.7): a zero on `a` survives every
  full-support self-model iff `θ_a(a ∧ O_d) = 0`; witnessed on the routing root (survives)
  and the coin-then-query tree (does not).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section general

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- **`θ_a`, weighted**: the total off-`d` weight (times `g`) of the `X`-leaves whose path
takes a `d`-edge labelled `a`. `g ≡ 1` gives CA-8′'s `θ_a(X)`, `g = payoff` its payoff form.
Both are functions of `C` off `d` only (`offWeight_congr_off`).
Source: CA-8′ (`∑_{q ∈ F_d} R_q θ_{q,a}`, summed over the fiber); mandate T7(b)
Kind: D -/
noncomputable def thetaW (d : ι) (a : acts d) (g : B.Leaves → K) (X : Finset Ω) : K :=
  ∑ ℓ ∈ (worldEv B X).filter (fun ℓ => (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ),
    offWeight C d B ℓ * g ℓ

/-- A leaf meeting no `d`-node has law `offWeight`. Source: none: infrastructure. Kind: L -/
theorem leafLaw_eq_offWeight_of_count_zero {d : ι} {ℓ : B.Leaves} (h : count d B ℓ = 0) :
    leafLaw C B ℓ = offWeight C d B ℓ := by
  have hnil : (draws B ℓ).filter (fun x => x.1 = d) = [] := by
    have := length_filter_draws d B ℓ
    rw [h] at this
    exact List.length_eq_zero_iff.mp this
  rw [List.filter_eq_nil_iff] at hnil
  have hfilt : (draws B ℓ).filter (fun x => x.1 ≠ d) = draws B ℓ := by
    rw [List.filter_eq_self]
    intro x hx
    have := hnil x hx
    simpa using this
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight offWeight
  rw [hfilt]

/-- A leaf meeting exactly one `d`-node takes exactly one `d`-edge.
Source: none: infrastructure. Kind: L -/
theorem exists_draw_of_count_one {d : ι} {ℓ : B.Leaves} (h : count d B ℓ = 1) :
    ∃ a : acts d, (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ ∧
      ∀ a', (⟨d, a'⟩ : Σ d, acts d) ∈ draws B ℓ → a' = a := by
  have hlen := length_filter_draws d B ℓ
  rw [h] at hlen
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hxmem : x ∈ (draws B ℓ).filter (fun y => y.1 = d) := by
    rw [hx]; exact List.mem_singleton_self x
  have hxd : x.1 = d := by simpa using (List.mem_filter.mp hxmem).2
  obtain ⟨d', a⟩ := x
  simp only at hxd
  subst hxd
  refine ⟨a, (List.mem_filter.mp hxmem).1, fun a' ha' => ?_⟩
  have : (⟨d', a'⟩ : Σ d, acts d) ∈ (draws B ℓ).filter (fun y => y.1 = d') :=
    List.mem_filter.mpr ⟨ha', by simp⟩
  rw [hx, List.mem_singleton] at this
  simpa using this

/-- `offWeight` ignores the deviation at `d`. Source: none: infrastructure. Kind: L -/
theorem offWeight_deviate (d : ι) (m : FinDistr K (acts d)) (ℓ : B.Leaves) :
    offWeight (C.deviate d m) d B ℓ = offWeight C d B ℓ :=
  offWeight_congr_off B d (fun d' hd' => Proc.deviate_ne C m hd') ℓ

/-- **The factorisation of the run law under a point-deviation** (CA-8′'s ratio formula,
weighted): at a point met at most once per run and covered for the uniform deviation, for
`X ⊆ O_d`, `∑_{λ⊨X} μ_{C[d↦m]}(ℓ) g(ℓ) = ∑_a m(a) θ_a^g(X)`. A leaf meeting no `d`-node is
null by coverage; a leaf meeting one takes a unique `d`-edge `a` and has law
`m(a) · offWeight_C(ℓ)`.
Source: CA-8′ ("`ν_{C'}(X | O_d) = ∑_q R_q ∑_a m(a) θ_{q,a}(X ∧ O_d) / …`"); mandate T7(b)
Kind: P
Fidelity: exact (fiber summed into `θ_a`)
Hyps: (a) `∀ ℓ, #_d(ℓ) ≤ 1`, (a) coverage for `C[d ↦ Unif]`, (a) `X ⊆ O_d` -/
theorem sum_leafLaw_deviate_eq (d : ι) (m : FinDistr K (acts d)) (g : B.Leaves → K)
    (X : Finset Ω) (hcount : ∀ ℓ, count d B ℓ ≤ 1)
    (hcov : Covers obs (C.deviate d FinDistr.uniform) B d) (hX : X ⊆ obs d) :
    ∑ ℓ ∈ worldEv B X, leafLaw (C.deviate d m) B ℓ * g ℓ = ∑ a, m.w a * thetaW C B d a g X := by
  unfold thetaW
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hoff := offWeight_deviate C B d m ℓ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hcount ℓ) with h0 | h1
  · have hnull : leafLaw (C.deviate d FinDistr.uniform) B ℓ = 0 := by
      by_contra hne
      have hpos : 0 < leafLaw (C.deviate d FinDistr.uniform) B ℓ :=
        lt_of_le_of_ne (leafLaw_nonneg _ B ℓ) (Ne.symm hne)
      have := hcov ℓ hpos (hX ((mem_worldEv B X ℓ).mp hℓ))
      omega
    rw [leafLaw_eq_offWeight_of_count_zero _ B h0, offWeight_deviate] at hnull
    rw [leafLaw_eq_offWeight_of_count_zero _ B h0, hoff, hnull, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro a _
    simp
  · obtain ⟨a₀, ha₀, huniq⟩ := exists_draw_of_count_one B h1
    rw [leafLaw_eq_w_mul_offWeight B _ h1 ha₀, Proc.deviate_same, hoff]
    rw [Finset.sum_eq_single a₀]
    · rw [if_pos ha₀]; ring
    · intro b _ hb
      rw [if_neg (fun h => hb (huniq b h))]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **`ν` under a point-deviation factors through `m`**: `ν_{C[d↦m]}(X ∩ O_d) = ∑_a m(a) θ_a(X ∩ O_d)`.
Source: CA-8′; mandate T7(b)
Kind: P
Fidelity: exact
Hyps: (a) `#_d ≤ 1`, (a) coverage for `C[d ↦ Unif]` -/
theorem nu_deviate_eq (d : ι) (m : FinDistr K (acts d)) (X : Finset Ω)
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d FinDistr.uniform) B d) :
    nu (C.deviate d m) B (X ∩ obs d) = ∑ a, m.w a * thetaW C B d a (fun _ => 1) (X ∩ obs d) := by
  rw [← sum_leafLaw_deviate_eq obs C B d m (fun _ => 1) (X ∩ obs d) hcount hcov
    Finset.inter_subset_right]
  simp [nu, mass]

/-- The payoff version. Source: CA-8′; mandate T7(b). Kind: P -/
theorem paySum_deviate_eq (d : ι) (m : FinDistr K (acts d)) (X : Finset Ω)
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d FinDistr.uniform) B d) :
    paySum (C.deviate d m) B (X ∩ obs d) = ∑ a, m.w a * thetaW C B d a (payoff B) (X ∩ obs d) :=
  sum_leafLaw_deviate_eq obs C B d m (payoff B) (X ∩ obs d) hcount hcov Finset.inter_subset_right

/-! ## The cancellation lemma -/

/-- Under leaf-level action veridicality and disjoint action events, `θ_{a'}` vanishes on any
sub-event of the `a`-event for `a' ≠ a`. Source: dp-cf-2-042. Kind: L -/
theorem thetaW_eq_zero_of_ne (d : ι)
    (hav : ∀ ℓ (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a'))
    (a a' : acts d) (hne : a' ≠ a) (g : B.Leaves → K) (Y : Finset Ω) (hY : Y ⊆ actEv d a) :
    thetaW C B d a' g Y = 0 := by
  unfold thetaW
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [Finset.mem_filter, mem_worldEv] at hℓ
  exact absurd (hY hℓ.1) (Finset.disjoint_left.mp (hdisj a' a hne) (hav ℓ a' hℓ.2))

/-- On a sub-event of `a ∧ O_d`, the deviation law is `m(a) · θ_a`.
Source: dp-cf-2-042 ("its law under `C[d ↦ m]` is `offWeight · m(a)`"); mandate T6(b)
Kind: P
Fidelity: exact -/
theorem sum_leafLaw_deviate_actEv (d : ι) (m : FinDistr K (acts d)) (g : B.Leaves → K)
    (a : acts d) (Y : Finset Ω) (hcount : ∀ ℓ, count d B ℓ ≤ 1)
    (hcov : Covers obs (C.deviate d FinDistr.uniform) B d)
    (hav : ∀ ℓ (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a'))
    (hYa : Y ⊆ actEv d a) (hYO : Y ⊆ obs d) :
    ∑ ℓ ∈ worldEv B Y, leafLaw (C.deviate d m) B ℓ * g ℓ = m.w a * thetaW C B d a g Y := by
  rw [sum_leafLaw_deviate_eq obs C B d m g Y hcount hcov hYO, Finset.sum_eq_single a]
  · intro b _ hb
    rw [thetaW_eq_zero_of_ne actEv C B d hav hdisj a b hb g Y hYa, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The cancellation lemma** (dp-cf-2-042, proved): at a point met at most once per run,
covered, with every `d`-edge action-veridical and disjoint action events, for every
self-model `m` and every `X`,
`ν_{C[d↦m]}(X ∩ a ∩ O_d) · ν_C(a ∩ O_d) = ν_C(X ∩ a ∩ O_d) · ν_{C[d↦m]}(a ∩ O_d)` —
both sides are `m(a) C(d)(a) θ_a(X ∩ a ∩ O_d) θ_a(a ∩ O_d)`.
Source: dp-cf-2-042 ("cancellation lemma … not adversarially re-reviewed"); zoo.md ZO-1
(amendment); mandate T6(b)
Kind: P
Fidelity: exact (hypotheses: `#_d ≤ 1` in place of `¬ Nested`, which it implies on the
positive leaves; coverage for the uniform deviation; leaf-level action veridicality)
Hyps: (a) all four -/
theorem cancellation (d : ι) (m : FinDistr K (acts d)) (a : acts d) (X : Finset Ω)
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d FinDistr.uniform) B d)
    (hav : ∀ ℓ (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a')) :
    nu (C.deviate d m) B (X ∩ actEv d a ∩ obs d) * nu C B (actEv d a ∩ obs d) =
      nu C B (X ∩ actEv d a ∩ obs d) * nu (C.deviate d m) B (actEv d a ∩ obs d) := by
  have key : ∀ (m' : FinDistr K (acts d)) (Y : Finset Ω), Y ⊆ actEv d a → Y ⊆ obs d →
      nu (C.deviate d m') B Y = m'.w a * thetaW C B d a (fun _ => 1) Y := fun m' Y hYa hYO => by
    rw [← sum_leafLaw_deviate_actEv obs actEv C B d m' (fun _ => 1) a Y hcount hcov hav hdisj hYa
      hYO]
    simp [nu, mass]
  have hself : C.deviate d (C d) = C := Function.update_eq_self d C
  have h1 := key m (X ∩ actEv d a ∩ obs d)
    (Finset.inter_subset_left.trans Finset.inter_subset_right) Finset.inter_subset_right
  have h2 := key (C d) (actEv d a ∩ obs d) Finset.inter_subset_left Finset.inter_subset_right
  have h3 := key (C d) (X ∩ actEv d a ∩ obs d)
    (Finset.inter_subset_left.trans Finset.inter_subset_right) Finset.inter_subset_right
  have h4 := key m (actEv d a ∩ obs d) Finset.inter_subset_left Finset.inter_subset_right
  rw [hself] at h2 h3
  rw [h1, h2, h3, h4]
  ring

/-- **Masked act values are self-model-free** where positive: `𝔼_{C[d↦m]}[r | a ∧ O_d] =
𝔼_C[r | a ∧ O_d]` under the cancellation hypotheses, whenever both conditioning events are
positive. So masked and limit EDT verdicts differ at most through `A_d^+`.
Source: dp-cf-2-042 (corollary); mandate T6(b)
Kind: C
Fidelity: exact
Hyps: (a) the cancellation hypotheses, (a) both positivities -/
theorem condExp_deviate_eq (d : ι) (m : FinDistr K (acts d)) (a : acts d)
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d FinDistr.uniform) B d)
    (hav : ∀ ℓ (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a'))
    (hm : 0 < nu (C.deviate d m) B (actEv d a ∩ obs d)) (hC : 0 < nu C B (actEv d a ∩ obs d)) :
    condExp (C.deviate d m) B (actEv d a ∩ obs d) = condExp C B (actEv d a ∩ obs d) := by
  have keyN : ∀ (m' : FinDistr K (acts d)),
      nu (C.deviate d m') B (actEv d a ∩ obs d) =
        m'.w a * thetaW C B d a (fun _ => 1) (actEv d a ∩ obs d) := fun m' => by
    rw [← sum_leafLaw_deviate_actEv obs actEv C B d m' (fun _ => 1) a _ hcount hcov hav hdisj
      Finset.inter_subset_left Finset.inter_subset_right]
    simp [nu, mass]
  have keyP : ∀ (m' : FinDistr K (acts d)),
      paySum (C.deviate d m') B (actEv d a ∩ obs d) =
        m'.w a * thetaW C B d a (payoff B) (actEv d a ∩ obs d) := fun m' =>
    sum_leafLaw_deviate_actEv obs actEv C B d m' (payoff B) a _ hcount hcov hav hdisj
      Finset.inter_subset_left Finset.inter_subset_right
  have hself : C.deviate d (C d) = C := Function.update_eq_self d C
  have hN := keyN (C d); have hP := keyP (C d)
  rw [hself] at hN hP
  have hma : m.w a ≠ 0 := by
    intro h; rw [keyN m, h, zero_mul] at hm; exact lt_irrefl 0 hm
  have hCa : (C d).w a ≠ 0 := by
    intro h; rw [hN, h, zero_mul] at hC; exact lt_irrefl 0 hC
  unfold condExp
  rw [keyN m, keyP m, hN, hP, mul_div_mul_left _ _ hma, mul_div_mul_left _ _ hCa]

/-! ## The manifold -/

/-- **Membership in `M_d` is masked clause 1**: `P_{s_d} ∈ M_d` iff some local full-support
self-model realizes `O_d` and `s_d` satisfies strict clause 1 under it.
Source: [[decision-problems-v2]] Q2; CA-8′; mandate T7(a)
Kind: L
Fidelity: exact -/
theorem maskedClause1_iff_mem_manifold (s : ι → State Ω K) (d : ι) :
    (∃ C', Admissible .LF C d C' ∧ 0 < nu C' B (obs d) ∧ StrictClause1At s obs C' B d) ↔
      (s d).pr ∈ manifold obs C B d := by
  simp only [manifold, Set.mem_setOf_eq, StrictClause1At]

/-! ## Self-transparency on the manifold -/

/-- **Recording from the veridicality package**: `#_d ≤ 1` and coverage for `C'` give exactly
one `d`-node on every positive `O_d`-run; subtree- and node-action-veridicality of every
`d`-node and disjoint action events give the remaining clauses of Definition 7.
Source: [[decision-problems-v2]] Definition 7; CA-8′(ii); mandate T7(c)
Kind: C
Fidelity: exact
Hyps: (a) all five -/
theorem recordsFor_of_veridical (C' : Proc ι acts K) (d : ι) (hcount : ∀ ℓ, count d B ℓ ≤ 1)
    (hcov : Covers obs C' B d) (hsv : ∀ q, pt B q = d → SubtreeVeridical obs B q)
    (hnav : ∀ q, pt B q = d → NodeActionVeridical actEv B q)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a')) :
    RecordsFor obs actEv C' B d := by
  intro ℓ hpos hO
  refine ⟨le_antisymm (hcount ℓ) (hcov ℓ hpos hO), fun q hq a hedge => ?_⟩
  refine ⟨hsv q hq, hnav q hq ℓ a hedge, fun a' ha' => ?_⟩
  subst hq
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj a' a hne) ha' (hnav q rfl ℓ a hedge)

/-- **Self-transparency on the manifold** (CA-8′(ii)): with every `d`-node subtree- and
action-veridical, `ν_{C[d↦m]}(a ∧ O_d) = m(a) · ν_{C[d↦m]}(O_d)` — the act credence of the
masked state equals the self-model.
Source: CA-8′(ii) ("`P(a | O_d) = m(a)`"); mandate T7(c)
Kind: C
Fidelity: exact
Hyps: (a) `#_d ≤ 1`, (a) coverage for `C[d ↦ m]`, (a) veridicality of every `d`-node,
(a) disjoint action events -/
theorem nu_deviate_actEv_eq_self (d : ι) (m : FinDistr K (acts d))
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d m) B d)
    (hsv : ∀ q, pt B q = d → SubtreeVeridical obs B q)
    (hnav : ∀ q, pt B q = d → NodeActionVeridical actEv B q)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a')) (a : acts d) :
    nu (C.deviate d m) B (actEv d a ∩ obs d) = m.w a * nu (C.deviate d m) B (obs d) := by
  have := nu_actEv_inter_obs_of_recordsFor obs actEv (C.deviate d m) B
    (recordsFor_of_veridical obs actEv B (C.deviate d m) d hcount hcov hsv hnav hdisj) a
  rwa [Proc.deviate_same] at this

/-! ## Which zeros survive -/

/-- **Which zeros survive** (Remark 3.7, CA-8′(iii)): under the cancellation hypotheses, a zero
on the act `a` survives every full-support self-model iff `θ_a(a ∧ O_d) = 0`. CA-8′(iii)
writes `θ_a(O_d)`; under action veridicality every leaf drawing `(d, a)` lies in the `a`-event,
so `θ_a(a ∧ O_d) = θ_a(O_d)` and the two readings agree.
Source: [[decision-problems-v2]] Remark 3.7; CA-8′(iii) ("a zero on `a` survives every
full-support `m` iff `θ_a(O_d) = 0`"); mandate T7(c)
Kind: C (one step over `sum_leafLaw_deviate_actEv`; regraded in repair round 2, adversarial N1)
Fidelity: exact
Hyps: (a) the cancellation hypotheses -/
theorem zero_survives_iff (d : ι) (a : acts d)
    (hcount : ∀ ℓ, count d B ℓ ≤ 1) (hcov : Covers obs (C.deviate d FinDistr.uniform) B d)
    (hav : ∀ ℓ (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a')) :
    (∀ m : FinDistr K (acts d), (∀ a', 0 < m.w a') →
        nu (C.deviate d m) B (actEv d a ∩ obs d) = 0) ↔
      thetaW C B d a (fun _ => 1) (actEv d a ∩ obs d) = 0 := by
  have key : ∀ (m' : FinDistr K (acts d)),
      nu (C.deviate d m') B (actEv d a ∩ obs d) =
        m'.w a * thetaW C B d a (fun _ => 1) (actEv d a ∩ obs d) := fun m' => by
    rw [← sum_leafLaw_deviate_actEv obs actEv C B d m' (fun _ => 1) a _ hcount hcov hav hdisj
      Finset.inter_subset_left Finset.inter_subset_right]
    simp [nu, mass]
  constructor
  · intro h
    have := h FinDistr.uniform (fun a' => FinDistr.uniform_w_pos a')
    rw [key] at this
    exact (mul_eq_zero.mp this).resolve_left (FinDistr.uniform_w_pos a).ne'
  · intro h m _
    rw [key, h, mul_zero]

end general

/-! ## Witnesses: the routing root and the coin-then-query tree -/

/-- On the routing root the zero on `b` survives: the `b`-edge leads off `O`, so
`θ_b(b ∧ O) = 0` (the event `b ∧ O` is empty).
Source: [[decision-problems-v2]] Remark 3.4, Remark 3.7; CA-11′ ("Routing root: `M_d` a point")
Kind: N+ -/
theorem routingRoot_zero_survives (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    thetaW (procQ q h0 h1) routingRoot () .b (fun _ => 1) (routeActEv () .b ∩ routeObs ()) = 0 := by
  unfold thetaW
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [Finset.mem_filter, mem_worldEv] at hℓ
  simp [routeActEv, routeObs] at hℓ

/-- A sum over the leaves of the coin-then-query tree. Source: none: infrastructure. Kind: L -/
theorem coinQuery_sum (f : coinQuery.Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold coinQuery at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- On the coin-then-query tree no zero survives: `θ_a(a ∧ O) = 1 > 0` for every `q`.
Source: mandate T7(c) ("`routingRoot` … versus `coinQuery`")
Kind: N+ -/
theorem coinQuery_theta_pos (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    0 < thetaW (procQ q h0 h1) coinQuery () .a (fun _ => 1) (cqActEv () .a ∩ cqObs ()) := by
  unfold thetaW worldEv
  rw [Finset.sum_filter, Finset.sum_filter, coinQuery_sum]
  simp [coinQuery, offWeight, cqActEv, cqObs, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair,
    FinDistr.coin]
  try norm_num

end Cleanroom.Decision.DpCalibLimits
