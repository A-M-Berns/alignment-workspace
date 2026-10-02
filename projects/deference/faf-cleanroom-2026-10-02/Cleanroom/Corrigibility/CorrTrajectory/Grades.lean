import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Cleanroom.Corrigibility.CorrJointProcess.Budget

/-!
# `corr-trajectory` — `Grades`: D1–D3 and Statement 1 (T2)

The grades of trajectory property over `ℕ → S` with the product topology: **tail** (membership
insensitive to finite changes), **safety** (every violation witnessed by a finite prefix) and
**liveness** (dense). Statement 1 of `invariant-final.md`, with the topology fixed (2-023) and the
finding sharpened:

* (a) a nonempty tail property is dense — **for every topology on `S`** (basic opens are finite-support
  cylinders; splice);
* (b) closed ⟹ safety for every `S`; for discrete `S`, safety ⟺ closed;
* (c) a tail property that is closed is `∅` or `univ` — again for every topology on `S` (the mandate's
  `[DiscreteTopology S]` is not needed);
* (d) **safety ⇏ closed for non-discrete `S`**: on `S = ℝ`, `{s ∣ s 0 ∈ (0, 1)}` is prefix-witnessed
  and not closed. So the develop file's D2 "closed in the product topology" was *stronger* than
  prefix-witnessing, not merely different; the direction the develop needed (closed ⟹ safety) holds
  generally;
* (e) Statement 1(c): `P(Φ) = 1 → P(Φ ∩ E) = P(E)` (Layer F); "absorption is not the only route" is
  `Potential.ville_finite`.

Trap avoided: the ambient instance on `ℕ → S` is always `Pi.topologicalSpace`; no
`DiscreteTopology (ℕ → S)` is ever in scope.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open Filter Topology Set

namespace Grades

variable {S : Type} [TopologicalSpace S]

/-- **D1, tail property**: membership is insensitive to finite changes.
Source: [[corr-wf14-inventory]] 071 / invariant-final.md D1
Kind: D
Fidelity: exact -/
def TailProp (Φ : Set (ℕ → S)) : Prop :=
  ∀ s s' : ℕ → S, (∀ᶠ t in atTop, s t = s' t) → (s ∈ Φ ↔ s' ∈ Φ)

/-- **D2, safety property (invariant)**: every violation is witnessed by a finite prefix.
Source: [[corr-wf14-inventory]] 071 / invariant-final.md D2
Kind: D
Fidelity: exact (prefix-witnessing; "closed in the product of discrete topologies" is `safety_iff_isClosed`) -/
def SafetyProp (Φ : Set (ℕ → S)) : Prop :=
  ∀ s ∉ Φ, ∃ N, ∀ s' : ℕ → S, (∀ t ≤ N, s' t = s t) → s' ∉ Φ

/-- **D3, liveness property**: every finite prefix extends into `Φ` — `Φ` is dense.
Source: [[corr-wf14-inventory]] 071 / invariant-final.md D3
Kind: D
Fidelity: exact -/
def LivenessProp (Φ : Set (ℕ → S)) : Prop := Dense Φ

/-- The splice of `p` on `[0, N]` with `s` after. Source: invariant-final.md proof of Statement 1(a). Kind: D. Fidelity: exact -/
def splice (p s : ℕ → S) (N : ℕ) : ℕ → S := fun t => if t ≤ N then p t else s t

/-- `splice_eventually_eq` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma splice_eventually_eq (p s : ℕ → S) (N : ℕ) : ∀ᶠ t in atTop, splice p s N t = s t :=
  eventually_atTop.2 ⟨N + 1, fun t ht => by simp [splice, show ¬ t ≤ N by omega]⟩

/-- **Statement 1(a): a nonempty tail property is dense — for every topology on `S`.** A basic open
set of the product topology constrains finitely many coordinates (`isOpen_pi_iff`); splice them onto
a member of `Φ`.
Source: [[corr-wf14-inventory]] 071, 2-023 / invariant-final.md Statement 1(a)
Kind: P (small)
Fidelity: stronger: every topology on `S`, not only the discrete one
Hyps: (a) only -/
theorem dense_of_tailProp {Φ : Set (ℕ → S)} (hΦ : TailProp Φ) (hne : Φ.Nonempty) : LivenessProp Φ := by
  obtain ⟨s, hs⟩ := hne
  rw [LivenessProp, dense_iff_inter_open]
  intro U hU ⟨u, hu⟩
  obtain ⟨I, v, hv, hsub⟩ := isOpen_pi_iff.1 hU u hu
  -- splice `u` on the finite index set `I` onto `s`
  let N := I.sup id
  refine ⟨splice u s N, hsub ?_, (hΦ (splice u s N) s (splice_eventually_eq u s N)).2 hs⟩
  intro i hi
  have hiN : i ≤ N := Finset.le_sup (f := id) hi
  simp only [splice, hiN, if_true]
  exact (hv i hi).2

/-- **Statement 1(b), first half: closed ⟹ safety, for every `S`.** The complement of a closed set is
open; a basic neighbourhood of a violator is a cylinder on finitely many coordinates, hence a prefix.
Source: [[corr-wf14-inventory]] 071, 2-023 / invariant-final.md D2 ("equivalently closed")
Kind: P (small)
Fidelity: stronger: every topology on `S`
Hyps: (a) only -/
theorem safetyProp_of_isClosed {Φ : Set (ℕ → S)} (hΦ : IsClosed Φ) : SafetyProp Φ := by
  intro s hs
  obtain ⟨I, v, hv, hsub⟩ := isOpen_pi_iff.1 hΦ.isOpen_compl s hs
  refine ⟨I.sup id, fun s' hs' => hsub fun i hi => ?_⟩
  rw [hs' i (Finset.le_sup (f := id) hi)]
  exact (hv i hi).2

/-- **Statement 1(b), second half: for discrete `S`, safety ⟹ closed.** The prefix cylinder
`{s' ∣ ∀ t ≤ N, s' t = s t}` is open (`isOpen_set_pi` with singleton opens).
Source: [[corr-wf14-inventory]] 071, 2-023 / invariant-final.md D2, adversary item 1
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem isClosed_of_safetyProp [DiscreteTopology S] {Φ : Set (ℕ → S)} (hΦ : SafetyProp Φ) : IsClosed Φ := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨N, hN⟩ := hΦ s hs
  refine ⟨(Finset.range (N + 1) : Set ℕ).pi fun t => {s t}, fun s' hs' => hN s' fun t ht => ?_, ?_, ?_⟩
  · have := hs' t (by simp [Nat.lt_succ_iff.2 ht])
    simpa using this
  · exact isOpen_set_pi (Finset.range (N + 1)).finite_toSet fun t _ => isOpen_discrete _
  · intro t _; simp

/-- **Statement 1(b): for discrete `S`, safety ⟺ closed** — the topology fix of 2-023.
Source: [[corr-wf14-inventory]] 071, 2-023 / invariant-final.md D2
Kind: C
Fidelity: exact -/
theorem safety_iff_isClosed [DiscreteTopology S] (Φ : Set (ℕ → S)) : SafetyProp Φ ↔ IsClosed Φ :=
  ⟨isClosed_of_safetyProp, safetyProp_of_isClosed⟩

/-- **Statement 1(b), the closed form: a closed tail property is `∅` or `univ`** — for every topology
on `S`. For discrete `S` "closed" is D2's safety (`safety_iff_isClosed`); for non-discrete `S` it is
strictly stronger (`safety_not_isClosed_real`), so 1(b) in D2's own vocabulary is the next theorem,
`tail_safety_trivial` (audit r2, fidelity N2). (The mandate's label for this item is "(c′)"; the
source's own is 1(b), which the ledger uses.)
Source: [[corr-wf14-inventory]] 071 / invariant-final.md Statement 1(b)
Kind: C (`dense_of_tailProp` + closed and dense)
Fidelity: variant: `IsClosed` in place of D2's prefix-witnessing (equivalent for discrete `S`; stronger hypothesis otherwise); every topology on `S`
Hyps: (a) only -/
theorem tail_isClosed_trivial {Φ : Set (ℕ → S)} (hΦ : TailProp Φ) (hc : IsClosed Φ) : Φ = ∅ ∨ Φ = univ := by
  rcases Φ.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · right
    have hd := dense_of_tailProp hΦ h
    rw [← hc.closure_eq]
    exact hd.closure_eq

/-- **Statement 1(b) in D2's vocabulary: a tail property that is a safety property (prefix-witnessed)
is `∅` or `univ`** — for every `S`, with no topology used: a point outside `Φ` has a witnessing
prefix, and splicing that prefix onto a point of `Φ` stays in `Φ` (tail) yet carries the prefix
(contradiction). Strictly stronger than `tail_isClosed_trivial` for non-discrete `S`.
Source: [[corr-wf14-inventory]] 071 / invariant-final.md Statement 1(b) ("a tail property is a safety property only if it is `∅` or `S^ℕ`"); audit r2 (fidelity N2)
Kind: P (small: the splice)
Fidelity: exact
Hyps: (a) only -/
theorem tail_safety_trivial {Φ : Set (ℕ → S)} (hΦ : TailProp Φ) (hs : SafetyProp Φ) :
    Φ = ∅ ∨ Φ = univ := by
  rcases Φ.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · exact Or.inl h
  · right
    rw [eq_univ_iff_forall]
    intro s
    by_contra hs'
    obtain ⟨N, hN⟩ := hs s hs'
    have h1 : splice s p N ∈ Φ := (hΦ (splice s p N) p (splice_eventually_eq s p N)).2 hp
    exact hN (splice s p N) (fun t ht => by simp [splice, ht]) h1

/-- **(d) Safety ⇏ closed for a non-discrete `S`**: on `S = ℝ` the set `{s ∣ s 0 ∈ (0, 1)}` is
prefix-witnessed (`N = 0`) and not closed (the sequence `s_n 0 = 1/(n+2)` converges to `s 0 = 0`).
So the develop's D2 ("closed in the product topology") was strictly stronger than prefix-witnessing.
Source: [[corr-wf14-inventory]] 2-023 / invariant-adversary.md item 1 (sharpened: one direction only)
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem safety_not_isClosed_real :
    SafetyProp {s : ℕ → ℝ | s 0 ∈ Ioo (0 : ℝ) 1} ∧ ¬ IsClosed {s : ℕ → ℝ | s 0 ∈ Ioo (0 : ℝ) 1} := by
  constructor
  · intro s hs
    refine ⟨0, fun s' hs' => ?_⟩
    simp only [mem_setOf_eq] at hs ⊢
    rwa [hs' 0 le_rfl]
  · intro hc
    -- the limit of `s_n := (1/(n+2), 0, 0, …)` is `0 ∉ Φ`
    have hmem : ∀ n : ℕ, (fun i : ℕ => if i = 0 then 1 / ((n : ℝ) + 2) else 0) ∈
        {s : ℕ → ℝ | s 0 ∈ Ioo (0 : ℝ) 1} := by
      intro n
      simp only [mem_setOf_eq, if_true, mem_Ioo]
      constructor
      · positivity
      · rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hlim : Tendsto (fun n : ℕ => fun i : ℕ => if i = 0 then 1 / ((n : ℝ) + 2) else 0) atTop
        (𝓝 (fun _ => (0 : ℝ))) := by
      rw [tendsto_pi_nhds]
      intro i
      by_cases hi : i = 0
      · simp only [hi, if_true]
        have : (fun n : ℕ => 1 / ((n : ℝ) + 2)) = fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
          funext n; push_cast; ring
        rw [this]
        exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
      · simp [hi]
    have := hc.mem_of_tendsto hlim (Eventually.of_forall hmem)
    simp at this

/-- **The N+ tail witness**: `{s ∣ ∀ᶠ t, s t = a}` is a tail property, nonempty, and (for discrete `S`
with a second point `b ≠ a`) not closed: `s_n = (b on [0, n], a after)` is in it and converges to
the constant `b`.
Source: mandate T2 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem eventually_const_tail [DiscreteTopology S] (a b : S) (hab : b ≠ a) :
    TailProp {s : ℕ → S | ∀ᶠ t in atTop, s t = a} ∧ ({s : ℕ → S | ∀ᶠ t in atTop, s t = a}).Nonempty ∧
      ¬ IsClosed {s : ℕ → S | ∀ᶠ t in atTop, s t = a} := by
  refine ⟨?_, ⟨fun _ => a, Eventually.of_forall fun _ => rfl⟩, ?_⟩
  · intro s s' h
    simp only [mem_setOf_eq]
    constructor
    · intro hs; filter_upwards [h, hs] with t ht hst; rwa [← ht]
    · intro hs; filter_upwards [h, hs] with t ht hst; rwa [ht]
  · intro hc
    have hmem : ∀ n : ℕ, (fun t : ℕ => if t ≤ n then b else a) ∈ {s : ℕ → S | ∀ᶠ t in atTop, s t = a} := by
      intro n
      exact eventually_atTop.2 ⟨n + 1, fun t ht => by simp [show ¬ t ≤ n by omega]⟩
    have hlim : Tendsto (fun n : ℕ => fun t : ℕ => if t ≤ n then b else a) atTop (𝓝 (fun _ => b)) := by
      rw [tendsto_pi_nhds]
      intro t
      refine tendsto_const_nhds.congr' ?_
      exact eventually_atTop.2 ⟨t, fun n hn => by simp [hn]⟩
    have := hc.mem_of_tendsto hlim (Eventually.of_forall hmem)
    simp only [mem_setOf_eq] at this
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    exact hab (hN N le_rfl)

end Grades

/-- **Statement 1(c), Layer F**: `P(Φ) = 1 → P(Φ ∩ E) = P(E)` — an almost-sure property is
consistent with every prefix event; the `0 < P(E)` of the source is idle (the identity holds
for every `E`).
Source: [[corr-wf14-inventory]] 071 / invariant-final.md Statement 1(c)
Kind: L
Fidelity: stronger: no positivity needed -/
theorem probOf_inter_of_ae {Ω : Type} [Fintype Ω] [DecidableEq Ω] (μ : FactoredSpaces.Distr Ω)
    (Φ E : Finset Ω) (h : Cleanroom.Corrigibility.CorrJointProcess.probOf μ Φ = 1) :
    Cleanroom.Corrigibility.CorrJointProcess.probOf μ (Φ ∩ E) =
      Cleanroom.Corrigibility.CorrJointProcess.probOf μ E := by
  open Cleanroom.Corrigibility.CorrJointProcess in
  have h1 : probOf μ (E \ (Φ ∩ E)) ≤ probOf μ Φᶜ :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun ω hω => by
      simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_inter] at hω ⊢
      exact fun hΦ => hω.2 ⟨hΦ, hω.1⟩) fun ω _ _ => μ.nonneg ω
  open Cleanroom.Corrigibility.CorrJointProcess in
  have h2 : probOf μ Φᶜ = 0 := by
    unfold probOf at *
    have := Finset.sum_add_sum_compl Φ μ.mass
    rw [μ.sum_eq_one] at this
    linarith
  open Cleanroom.Corrigibility.CorrJointProcess in
  have h3 : probOf μ E = probOf μ (Φ ∩ E) + probOf μ (E \ (Φ ∩ E)) := by
    unfold probOf
    rw [add_comm, Finset.sum_sdiff Finset.inter_subset_right]
  open Cleanroom.Corrigibility.CorrJointProcess in
  have h4 : 0 ≤ probOf μ (E \ (Φ ∩ E)) := Finset.sum_nonneg fun ω _ => μ.nonneg ω
  linarith

end Cleanroom.Corrigibility.CorrTrajectory
