import Cleanroom.Udt.UdtPolicyCalc.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Local versus global optimality: T2–T5

* T2 `isLocalOptimum_of_isOptimal`: global ⟹ local (the corpus's "verified chain"; Kind T).
* T3 `coordButtons_*`: local ⇏ global, the Coordinated-Buttons witness (Kind P + N+), with
  `coordButtons_not_separable` as the non-vacuity check of `CrossSituationDependence`.
* T4 (a) `separable_of_rtest` / `Separable.exists_rtest` (the two corpus definitions of
  cross-situation dependence related); (b) `fsaDependence_iff_nonconstant` (the literal
  formal-single-agent predicate is non-constancy on `|S| ≥ 2`; refuted as a definition);
  (c) `weighted_sum_le_sum_sup'`, `weighted_sum_sup'_eq_sup'_sum` and their `FinDist` instances
  (Diffractor's lookup-table identity); (d) `Separable.isOptimal_of_isLocalOptimum` and
  `sup'_eq_sum_sup'_of_separable` (`max = Σ max`, derived from (c) with unit weights).
* T5 (extension): `Separable.ordSep`, `OrdSep.localGlobal`, the refutation of necessity
  (`localGlobal_U5a`, `U5a_not_separable`) and the separation of `OrdSep` from `LocalGlobal`
  (`localGlobal_U5b`, `U5b_not_ordSep`).

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

open Finset

section Basic

variable {S A : Type} [DecidableEq S]

/-- **T2 (udt-rep-002).** A globally optimal policy is a local optimum: `π(s) ∈ argmax_a U(π[s ↦ a])`
for every `s`. Proof: `Function.update_eq_self` plus the hypothesis at `π[s ↦ a']`. The corpus
calls this "the UDT formula"; the identification of `argmax_a U(π[s ↦ a])` with
`argmax_a E[U | π(s) = a]` is `Simplification.lean`'s business and fails in general.
Source: `lean/UDT/Theorem.lean:30–46` (udt-rep-002); [[critical-analysis]] "What we can actually prove"
Kind: T
Fidelity: exact
Hyps: (a) none beyond `IsOptimal U π` -/
theorem isLocalOptimum_of_isOptimal {U : Policy S A → ℝ} {π : Policy S A} (h : IsOptimal U π) :
    IsLocalOptimum U π := by
  intro s a'
  rw [Function.update_eq_self]
  exact h _

end Basic

section Separability

variable {S A : Type} [Fintype S]

/-- A separable sum after a one-situation modification: `∑ t, u t (π[s ↦ a] t) = ∑ t, u t (π t) - u s (π s) + u s a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_update_eq [DecidableEq S] (u : S → A → ℝ) (π : Policy S A) (s : S) (a : A) :
    ∑ t, u t (Function.update π s a t) = ∑ t, u t (π t) - u s (π s) + u s a := by
  have h1 : ∑ t, u t (Function.update π s a t) = u s a + ∑ t ∈ univ.erase s, u t (π t) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ s), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun t ht => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  have h2 : ∑ t, u t (π t) = u s (π s) + ∑ t ∈ univ.erase s, u t (π t) :=
    (Finset.add_sum_erase _ _ (mem_univ s)).symm
  rw [h1, h2]
  ring

/-- A `P`-weighted separable form `U π = ∑ s, P s * u s (π s)` is separable (the weight is
absorbed into `u`); conversely `Separable` is the `P ≡ 1` case.
Source: [[formal-single-agent]] "When do split and unified agree?" (udt-rep-047)
Kind: L
Fidelity: exact
Hyps: none -/
theorem separable_of_weighted {U : Policy S A → ℝ} (P : S → ℝ) (u : S → A → ℝ)
    (h : ∀ π, U π = ∑ s, P s * u s (π s)) : Separable U :=
  ⟨fun s a => P s * u s a, h⟩

/-- **T4(a), one direction.** Per-situation rewards passing the policy-dependence test give a
separable policy utility.
Source: [[when-udt-edt-diverge]] "When are they the same?"; [[formal-single-agent]] (udt-rep-047)
Kind: P
Fidelity: exact
Hyps: (a) none beyond `RTest R` -/
theorem separable_of_rtest {R : S → Policy S A → ℝ} (hR : RTest R) :
    Separable (fun π => ∑ s, R s π) :=
  ⟨fun s a => R s (fun _ => a), fun π => Finset.sum_congr rfl fun s _ => hR s π (fun _ => π s) rfl⟩

/-- **T4(a), converse.** A separable `U` admits a presentation `U π = ∑ s, R s π` by per-situation
rewards passing the policy-dependence test (`R s π := u s (π s)`). The two corpus definitions
are equivalent only *given* a presentation of `U` as a sum of per-situation rewards: every `U`
has some such presentation (e.g. `R s π := U π / |S|`), and it is the existence of an `RTest`
presentation that separability amounts to.
Source: [[topics/policy-types]]; [[when-udt-edt-diverge]] (udt-rep-047, the "not shown equivalent" flag)
Kind: P
Fidelity: exact
Hyps: (a) none beyond `Separable U` -/
theorem Separable.exists_rtest {U : Policy S A → ℝ} (h : Separable U) :
    ∃ R : S → Policy S A → ℝ, RTest R ∧ ∀ π, U π = ∑ s, R s π := by
  obtain ⟨u, hu⟩ := h
  exact ⟨fun s π => u s (π s), fun s π π' hs => by simp [hs], hu⟩

/-- **T4(b), the refutation.** The literal formal-single-agent predicate holds for every
non-constant `U` as soon as there are two situations: if `π, π'` with `U π ≠ U π'` agree
somewhere, done; if they disagree everywhere, `π'' := π[s₀ ↦ π' s₀]` agrees with `π` at `s₁` and
with `π'` at `s₀`, and one of the two pairs has different values.
Source: [[formal-single-agent]] lines 61–71 (udt-rep-047; mandate T4(b))
Kind: P
Fidelity: exact (refutation of the literal definition)
Hyps: (a) none -/
theorem fsaDependence_of_nonconstant [DecidableEq S] {U : Policy S A → ℝ} (hS : ∃ s₀ s₁ : S, s₀ ≠ s₁)
    (hU : ∃ π π', U π ≠ U π') : FSADependence U := by
  obtain ⟨s₀, s₁, hne⟩ := hS
  obtain ⟨π, π', hπ⟩ := hU
  by_cases hagree : ∃ s, π s = π' s
  · obtain ⟨s, hs⟩ := hagree
    exact ⟨s, π, π', hs, hπ⟩
  · by_cases h2 : U (Function.update π s₀ (π' s₀)) = U π
    · refine ⟨s₀, Function.update π s₀ (π' s₀), π', by simp, ?_⟩
      rw [h2]
      exact hπ
    · refine ⟨s₁, π, Function.update π s₀ (π' s₀), ?_, fun h => h2 h.symm⟩
      rw [Function.update_of_ne hne.symm]

omit [Fintype S] in
/-- Conversely the literal predicate implies non-constancy (trivially).
Source: [[formal-single-agent]] lines 61–71
Kind: L
Fidelity: exact
Hyps: none -/
theorem nonconstant_of_fsaDependence {U : Policy S A → ℝ} (h : FSADependence U) :
    ∃ π π', U π ≠ U π' := by
  obtain ⟨_, π, π', _, h⟩ := h
  exact ⟨π, π', h⟩

/-- **T4(b) as an equivalence.** On `|S| ≥ 2` the literal formal-single-agent definition of
cross-situation dependence *is* non-constancy of `U` — separable utilities included. The
surviving neighbour is `CrossSituationDependence := ¬ Separable` (Defs).
Source: [[formal-single-agent]] lines 61–71 (udt-rep-047; mandate §7 item 5)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fsaDependence_iff_nonconstant [DecidableEq S] {U : Policy S A → ℝ} (hS : ∃ s₀ s₁ : S, s₀ ≠ s₁) :
    FSADependence U ↔ ∃ π π', U π ≠ U π' :=
  ⟨nonconstant_of_fsaDependence, fsaDependence_of_nonconstant hS⟩

end Separability

/-! ### T4(c): the lookup-table identity -/

section Lookup

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

omit [DecidableEq X] in
/-- **T4(c)(i), weighted form.** `∑ x, w x * f x y ≤ ∑ x, w x * max_y' f x y'` for non-negative
weights: a fixed choice is beaten by the pointwise maximum.
Source: `references/udt101/03-plannable-unplanned.md` lines 35–37 (udt-rep-2-021)
Kind: P
Fidelity: exact (for any non-negative weights; the distribution case is `FinDist.exp_le_exp_sup'`)
Hyps: (a) none -/
theorem weighted_sum_le_sum_sup' (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f : X → Y → ℝ) (y : Y) :
    ∑ x, w x * f x y ≤ ∑ x, w x * univ.sup' univ_nonempty (f x) :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (Finset.le_sup' (f x) (mem_univ y)) (hw x)

/-- **T4(c)(ii), weighted form (the lookup-table identity).** For non-negative weights,
`∑ x, w x * max_y f x y = max_{g : X → Y} ∑ x, w x * f x (g x)`: the pointwise argmax is an
optimal lookup table, *because the weights do not depend on `g`*.
Source: `references/udt101/03-plannable-unplanned.md` lines 39–41 (udt-rep-2-021)
Kind: P
Fidelity: exact (any non-negative weights; unit weights give `max = Σ max`, T4(d))
Hyps: (a) none -/
theorem weighted_sum_sup'_eq_sup'_sum (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f : X → Y → ℝ) :
    ∑ x, w x * univ.sup' univ_nonempty (f x) =
      univ.sup' univ_nonempty (fun g : X → Y => ∑ x, w x * f x (g x)) := by
  apply le_antisymm
  · choose g hg using fun x => Finset.exists_mem_eq_sup' (univ_nonempty : (univ : Finset Y).Nonempty) (f x)
    calc ∑ x, w x * univ.sup' univ_nonempty (f x) = ∑ x, w x * f x (g x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [(hg x).2]
      _ ≤ _ := Finset.le_sup' (fun g : X → Y => ∑ x, w x * f x (g x)) (mem_univ g)
  · apply Finset.sup'_le
    intro g _
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' (f x) (mem_univ (g x))) (hw x)

omit [DecidableEq X] in
/-- **T4(c)(i).** `max_y E_μ[f(·, y)] ≤ E_μ[max_y f(x, y)]` (for each `y`).
Source: `references/udt101/03-plannable-unplanned.md` lines 35–37 (udt-rep-2-021)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem FinDist.exp_le_exp_sup' (μ : FinDist X) (f : X → Y → ℝ) (y : Y) :
    μ.exp (fun x => f x y) ≤ μ.exp (fun x => univ.sup' univ_nonempty (f x)) :=
  weighted_sum_le_sum_sup' μ.w μ.nonneg f y

/-- **T4(c)(ii).** `E_μ[max_y f(x, y)] = max_{g : X → Y} E_μ[f(x, g x)]`.
Source: `references/udt101/03-plannable-unplanned.md` lines 39–41 (udt-rep-2-021)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem FinDist.exp_sup'_eq_sup'_exp (μ : FinDist X) (f : X → Y → ℝ) :
    μ.exp (fun x => univ.sup' univ_nonempty (f x)) =
      univ.sup' univ_nonempty (fun g : X → Y => μ.exp (fun x => f x (g x))) :=
  weighted_sum_sup'_eq_sup'_sum μ.w μ.nonneg f

end Lookup

/-! ### T4(d): local ⟹ global under separability -/

section LocalGlobalSep

variable {S A : Type} [Fintype S] [DecidableEq S]

/-- **T4(d) (udt-rep-003(b), 047).** Under separability, every local optimum is a global optimum:
local optimality at `s` pins `u s (π s) ≥ u s a` for every `a`, and the sum of pointwise maxima
is the maximum of the sum. The failure of the conclusion without the hypothesis is T3.
Source: [[formal-single-agent]] "When do split and unified agree?"; `lean/UDT/Theorem.lean:48–101`
(the source sets up `diffObs` "for a converse" and stops) (udt-rep-003(b), 047)
Kind: P
Fidelity: exact
Hyps: (a) none beyond `Separable U`, `IsLocalOptimum U π` -/
theorem Separable.isOptimal_of_isLocalOptimum {U : Policy S A → ℝ} (hU : Separable U)
    {π : Policy S A} (h : IsLocalOptimum U π) : IsOptimal U π := by
  obtain ⟨u, hu⟩ := hU
  intro π'
  rw [hu, hu]
  apply Finset.sum_le_sum
  intro s _
  have := (isLocalOptimum_iff.mp h) s (π' s)
  rw [hu, hu, sum_update_eq] at this
  linarith

/-- Separability implies the local ⟹ global property.
Source: [[formal-single-agent]] (udt-rep-003(b))
Kind: L
Fidelity: exact
Hyps: none -/
theorem Separable.localGlobal {U : Policy S A → ℝ} (hU : Separable U) : LocalGlobal U :=
  fun _ h => hU.isOptimal_of_isLocalOptimum h

/-- **T4(d), the `max = Σ max` formula.** For a separable `U π = ∑ s, u s (π s)`,
`max_π U π = ∑ s, max_a u s a`. Derived from the lookup-table identity with unit weights,
not re-proved. (The corpus's `P`-weighted version is the case `u s a := P s * u' s a`.)
Source: [[formal-single-agent]] lines 139–147; [[when-udt-edt-diverge]] lines 50–56 (udt-rep-047, 2-031(a))
Kind: C
Fidelity: exact
Hyps: (a) none beyond the presentation `hu` -/
theorem sup'_eq_sum_sup'_of_separable [Fintype A] [Nonempty A] (u : S → A → ℝ) (U : Policy S A → ℝ)
    (hu : ∀ π, U π = ∑ s, u s (π s)) :
    univ.sup' univ_nonempty U = ∑ s, univ.sup' univ_nonempty (u s) := by
  have key := weighted_sum_sup'_eq_sup'_sum (fun _ : S => (1 : ℝ)) (fun _ => zero_le_one) u
  simp only [one_mul] at key
  rw [key]
  congr 1
  funext π
  exact hu π

/-- **T5, the easy inclusion.** Separable ⟹ ordinally separable: the comparison of `a` and `a'`
at `s` is `u s a ≤ u s a'`, independent of the rest of the policy.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond `Separable U` -/
theorem Separable.ordSep {U : Policy S A → ℝ} (h : Separable U) : OrdSep U := by
  obtain ⟨u, hu⟩ := h
  intro s a a' π π'
  simp only [hu, sum_update_eq]
  constructor <;> intro h <;> linarith

/-- **T5, the sufficient condition.** Ordinal separability implies local ⟹ global: walk from a
local optimum `π` to any `π'` one disagreeing coordinate at a time; each step is weakly
non-improving by `OrdSep` transported from `π`'s local optimality. Induction on the number of
disagreeing coordinates (the source's orphan `modify_reduces_diff` is this induction's measure).
Source: [[udt-policy-calc-mandate]] §5 (extension; not in any source)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond `OrdSep U` -/
theorem OrdSep.localGlobal {U : Policy S A → ℝ} (hU : OrdSep U) : LocalGlobal U := by
  classical
  intro π hπ
  have key : ∀ n : ℕ, ∀ π' : Policy S A,
      (univ.filter fun s => π s ≠ π' s).card = n → U π' ≤ U π := by
    intro n
    induction n with
    | zero =>
      intro π' hcard
      have : π' = π := by
        funext s
        by_contra hne
        have hmem : s ∈ univ.filter fun s => π s ≠ π' s := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Ne.symm hne
        rw [Finset.card_eq_zero] at hcard
        simp [hcard] at hmem
      rw [this]
    | succ n ih =>
      intro π' hcard
      have hne : (univ.filter fun s => π s ≠ π' s).Nonempty := by
        rw [← Finset.card_pos, hcard]
        exact Nat.succ_pos n
      obtain ⟨s₀, hs₀⟩ := hne
      have hfilt : (univ.filter fun s => π s ≠ Function.update π' s₀ (π s₀) s) =
          (univ.filter fun s => π s ≠ π' s).erase s₀ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases ht : t = s₀
        · subst ht
          simp
        · simp [Function.update_of_ne ht, ht]
      have hcard' : (univ.filter fun s => π s ≠ Function.update π' s₀ (π s₀) s).card = n := by
        rw [hfilt, Finset.card_erase_of_mem hs₀, hcard]
        simp
      have h1 : U (Function.update π' s₀ (π s₀)) ≤ U π := ih _ hcard'
      have h2 : U π' ≤ U (Function.update π' s₀ (π s₀)) := by
        have hπ'eq : π' = Function.update (Function.update π' s₀ (π s₀)) s₀ (π' s₀) := by
          rw [Function.update_idem, Function.update_eq_self]
        have hπ''eq : Function.update π' s₀ (π s₀) =
            Function.update (Function.update π' s₀ (π s₀)) s₀ (π s₀) := by
          rw [Function.update_idem]
        have hloc : U (Function.update π s₀ (π' s₀)) ≤ U (Function.update π s₀ (π s₀)) :=
          hπ s₀ (π' s₀)
        have := (hU s₀ (π' s₀) (π s₀) (Function.update π' s₀ (π s₀)) π).mpr hloc
        rw [← hπ'eq, ← hπ''eq] at this
        exact this
      exact h2.trans h1
  exact fun π' => key _ π' rfl

end LocalGlobalSep

/-! ### Two-situation, two-action tables and the witnesses -/

section Fin2

/-- A policy utility on `Fin 2 → Fin 2` given by its four values `v00 v01 v10 v11`
(`vij := U (π 0 = i, π 1 = j)`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def tbl (v00 v01 v10 v11 : ℝ) (π : Fin 2 → Fin 2) : ℝ :=
  if π 0 = 0 then (if π 1 = 0 then v00 else v01) else (if π 1 = 0 then v10 else v11)

/-- Supporting lemma `tbl_00` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem tbl_00 (v00 v01 v10 v11 : ℝ) : tbl v00 v01 v10 v11 ![0, 0] = v00 := by simp [tbl]
/-- Supporting lemma `tbl_01` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem tbl_01 (v00 v01 v10 v11 : ℝ) : tbl v00 v01 v10 v11 ![0, 1] = v01 := by simp [tbl]
/-- Supporting lemma `tbl_10` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem tbl_10 (v00 v01 v10 v11 : ℝ) : tbl v00 v01 v10 v11 ![1, 0] = v10 := by simp [tbl]
/-- Supporting lemma `tbl_11` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem tbl_11 (v00 v01 v10 v11 : ℝ) : tbl v00 v01 v10 v11 ![1, 1] = v11 := by simp [tbl]

/-- Supporting lemma `policy2_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policy2_eq (π : Fin 2 → Fin 2) : π = ![π 0, π 1] := by
  funext i
  fin_cases i <;> rfl

/-- Quantification over the four policies `Fin 2 → Fin 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem forall_policy2 {P : (Fin 2 → Fin 2) → Prop} :
    (∀ π, P π) ↔ P ![0, 0] ∧ P ![0, 1] ∧ P ![1, 0] ∧ P ![1, 1] := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h00, h01, h10, h11⟩ π
    have key : ∀ a b : Fin 2, P ![a, b] := by
      simp only [Fin.forall_fin_two]
      exact ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
    rw [policy2_eq π]
    exact key _ _

/-- Supporting lemma `update_vec2_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem update_vec2_zero {α : Type} (a b c : α) :
    Function.update ![a, b] (0 : Fin 2) c = ![c, b] := by
  funext i
  fin_cases i <;> simp

/-- Supporting lemma `update_vec2_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem update_vec2_one {α : Type} (a b c : α) :
    Function.update ![a, b] (1 : Fin 2) c = ![a, c] := by
  funext i
  fin_cases i <;> simp

/-- Supporting lemma `piFinTwoEquiv_symm_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem piFinTwoEquiv_symm_eq {α : Type} (a b : α) :
    (piFinTwoEquiv fun _ => α).symm (a, b) = ![a, b] := by
  funext i
  fin_cases i <;> rfl

/-- A sum over the four policies `Fin 2 → Fin 2`, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policy2_sum {M : Type} [AddCommMonoid M] (g : (Fin 2 → Fin 2) → M) :
    ∑ π, g π = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, piFinTwoEquiv_symm_eq, add_assoc]

/-- On `Fin 2 → A`, a separable utility satisfies the exchange identity
`U π + U π' = U (π[1 ↦ π' 1]) + U (π'[1 ↦ π 1])`; its failure witnesses non-separability.
Source: none: infrastructure (T3's non-vacuity check)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem Separable.exchange {A : Type} {U : Policy (Fin 2) A → ℝ} (h : Separable U)
    (π π' : Policy (Fin 2) A) :
    U π + U π' = U (Function.update π 1 (π' 1)) + U (Function.update π' 1 (π 1)) := by
  obtain ⟨u, hu⟩ := h
  simp only [hu, Fin.sum_univ_two, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  ring

/-- **Coordinated Buttons**: two rooms, both press the same button — \$5 each for button `0`,
\$10 each for button `1`, nothing for a mismatch.
Source: [[examples-revisited]] / [[gap1-reframing-predictor-access]] §8 table (udt-rep-003(a), 2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
def coordButtons : Policy (Fin 2) (Fin 2) → ℝ := tbl 5 0 0 10

/-- **T3 (udt-rep-003(a)).** `const 0` is a local optimum of Coordinated Buttons: either
unilateral change gives `0 < 5`.
Source: `lean/UDT/Theorem.lean:48–101` sets up a converse and stops; the corpus never states this
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_localOptimum : IsLocalOptimum coordButtons ![0, 0] := by
  rw [isLocalOptimum_iff]
  simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, coordButtons, tbl_00, tbl_01,
    tbl_10, tbl_11]
  norm_num

/-- **T3.** `const 0` is not optimal: `const 1` scores `10 > 5`.
Source: as `coordButtons_localOptimum`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_not_optimal : ¬ IsOptimal coordButtons ![0, 0] := by
  intro h
  have := h ![1, 1]
  simp only [coordButtons, tbl_00, tbl_11] at this
  norm_num at this

/-- **T3, headline (udt-rep-003(a)).** Local optimality does not imply global optimality: the
UDT local formula does not pin down the policy (the "equilibrium-selection problem").
Source: `lean/UDT/Theorem.lean:48–101` (converse left open); [[examples-revisited]] (udt-rep-003(a), 2-018)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_localOptimum_not_optimal :
    ∃ (U : Policy (Fin 2) (Fin 2) → ℝ) (π : Policy (Fin 2) (Fin 2)),
      IsLocalOptimum U π ∧ ¬ IsOptimal U π :=
  ⟨coordButtons, ![0, 0], coordButtons_localOptimum, coordButtons_not_optimal⟩

/-- **T3, non-vacuity of `CrossSituationDependence`.** Coordinated Buttons is not separable
(the exchange identity would force `5 + 10 = 0 + 0`); T4(d)'s hypothesis genuinely fails there.
Source: mandate T3 (non-vacuity check for T4(a)'s definition)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_not_separable : CrossSituationDependence coordButtons := by
  intro h
  have := h.exchange ![0, 0] ![1, 1]
  simp only [update_vec2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, coordButtons, tbl_00,
    tbl_01, tbl_10, tbl_11] at this
  norm_num at this

/-- Coordinated Buttons has two genuine local optima (`const 0` and `const 1`).
Source: mandate T3 (grade N+: "two genuine local optima")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_localOptimum_one : IsLocalOptimum coordButtons ![1, 1] := by
  rw [isLocalOptimum_iff]
  simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, coordButtons, tbl_00, tbl_01,
    tbl_10, tbl_11]
  norm_num

/-- The separable utility `U π = [π 0 = 1] + [π 1 = 1]` on `Fin 2 → Fin 2`.
Source: mandate T4(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def sepIndicator : Policy (Fin 2) (Fin 2) → ℝ := tbl 0 1 1 2

/-- Supporting lemma `sepIndicator_separable` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sepIndicator_separable : Separable sepIndicator := by
  refine ⟨fun _ a => if a = 1 then 1 else 0, ?_⟩
  rw [forall_policy2]
  simp only [sepIndicator, tbl_00, tbl_01, tbl_10, tbl_11, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  norm_num

/-- **T4(b), the instance.** The separable `sepIndicator` satisfies the literal formal-single-agent
predicate (`π = (1,0)` and `π' = (1,1)` agree at `0` and score `1 ≠ 2`): the definition counts a
separable utility as cross-situation dependent.
Source: [[formal-single-agent]] lines 61–71 (udt-rep-047; mandate T4(b))
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fsaDependence_sepIndicator : FSADependence sepIndicator :=
  ⟨0, ![1, 0], ![1, 1], by simp, by
    simp only [sepIndicator, tbl_10, tbl_11]
    norm_num⟩

/-- **T4(d) witness.** The pointwise argmax `const 1` of `sepIndicator` is a local optimum, hence
(by `Separable.isOptimal_of_isLocalOptimum`) a global one; `sepIndicator` is non-constant.
Source: mandate T4(d) witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sepIndicator_localOptimum : IsLocalOptimum sepIndicator ![1, 1] := by
  rw [isLocalOptimum_iff]
  simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, sepIndicator, tbl_00, tbl_01,
    tbl_10, tbl_11]
  norm_num

/-- Supporting lemma `sepIndicator_optimal` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sepIndicator_optimal : IsOptimal sepIndicator ![1, 1] :=
  sepIndicator_separable.isOptimal_of_isLocalOptimum sepIndicator_localOptimum

/-- Supporting lemma `sepIndicator_nonconstant` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sepIndicator_nonconstant : sepIndicator ![0, 0] ≠ sepIndicator ![1, 1] := by
  simp only [sepIndicator, tbl_00, tbl_11]
  norm_num

/-! ### T5: separability is not necessary for local ⟹ global -/

/-- `U (0,0) = 0`, `U (1,0) = 1`, `U (0,1) = 1`, `U (1,1) = 3`: the unique local optimum is the
global one, yet `U` is not separable.
Source: [[udt-policy-calc-mandate]] §5
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U5a : Policy (Fin 2) (Fin 2) → ℝ := tbl 0 1 1 3

/-- **T5, refutation of necessity (i).** `U5a` has the local ⟹ global property.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem localGlobal_U5a : LocalGlobal U5a := by
  unfold LocalGlobal
  rw [forall_policy2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5a, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5a, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5a, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro _
    rw [IsOptimal, forall_policy2]
    simp only [U5a, tbl_00, tbl_01, tbl_10, tbl_11]
    norm_num

/-- **T5, refutation of necessity (ii).** `U5a` is not separable: additivity would force
`U(0,0) + U(1,1) = U(0,1) + U(1,0)`, i.e. `3 = 2`.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem U5a_not_separable : ¬ Separable U5a := by
  intro h
  have := h.exchange ![0, 0] ![1, 1]
  simp only [update_vec2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, U5a, tbl_00, tbl_01,
    tbl_10, tbl_11] at this
  norm_num at this

/-- **T5, headline.** Separability is not necessary for local ⟹ global on finite situation sets.
Source: [[udt-policy-calc-mandate]] §5 (extension; the plan's "is additivity necessary?")
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem exists_localGlobal_not_separable :
    ∃ U : Policy (Fin 2) (Fin 2) → ℝ, LocalGlobal U ∧ ¬ Separable U :=
  ⟨U5a, localGlobal_U5a, U5a_not_separable⟩

/-- `U5a` is ordinally separable (so it does not separate `OrdSep` from `Separable`'s consequence).
Source: [[udt-policy-calc-mandate]] §5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem U5a_ordSep : OrdSep U5a := by
  simp only [OrdSep, Fin.forall_fin_two, forall_policy2, update_vec2_zero, update_vec2_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, U5a, tbl_00, tbl_01, tbl_10,
    tbl_11]
  norm_num

/-- `U (0,0) = 0`, `U (1,0) = 1`, `U (0,1) = -1`, `U (1,1) = 2`: unique local optimum `(1,1)`, but the
sign of the `s = 1` comparison depends on `π 0`.
Source: [[udt-policy-calc-mandate]] §5
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U5b : Policy (Fin 2) (Fin 2) → ℝ := tbl 0 (-1) 1 2

/-- **T5.** `U5b` has the local ⟹ global property.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem localGlobal_U5b : LocalGlobal U5b := by
  unfold LocalGlobal
  rw [forall_policy2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5b, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5b, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro h
    rw [isLocalOptimum_iff] at h
    simp only [Fin.forall_fin_two, update_vec2_zero, update_vec2_one, U5b, tbl_00, tbl_01, tbl_10,
      tbl_11] at h
    norm_num at h
  · intro _
    rw [IsOptimal, forall_policy2]
    simp only [U5b, tbl_00, tbl_01, tbl_10, tbl_11]
    norm_num

/-- **T5.** `U5b` is not ordinally separable: at `s = 1`, `0 ≤ -1` fails with `π 0 = 0` while
`1 ≤ 2` holds with `π 0 = 1`.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem U5b_not_ordSep : ¬ OrdSep U5b := by
  intro h
  have := h 1 0 1 ![0, 0] ![1, 0]
  simp only [update_vec2_one, U5b, tbl_00, tbl_01, tbl_10, tbl_11] at this
  norm_num at this

/-- **T5, headline.** Ordinal separability is sufficient but not necessary for local ⟹ global:
`Separable ⊊ OrdSep ⊊ LocalGlobal` on finite situation sets.
Source: [[udt-policy-calc-mandate]] §5 (extension)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem exists_localGlobal_not_ordSep :
    ∃ U : Policy (Fin 2) (Fin 2) → ℝ, LocalGlobal U ∧ ¬ OrdSep U :=
  ⟨U5b, localGlobal_U5b, U5b_not_ordSep⟩

end Fin2

end

end Cleanroom.Udt.UdtPolicyCalc
