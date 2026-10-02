import Cleanroom.Udt.UdtInfluence101.Defs

/-!
# `Cleanroom.Udt.UdtInfluence101.Atoms`: the filtration, measurability, the averaged algorithm

Infrastructure lemmas for the play space of `Defs`: the time-`n` atoms form a refining sequence of
partitions; every time-`n` quantity (`pr`, `cexp`, the influences) is `𝔽_n`-measurable; the
averaged algorithm `avg A h n` is `𝔽_n`-measurable at `h`, equals `A` at the horizon `n = |h|`,
fixes constant algorithms (`avg_ofDist`, Post 8 Lemma 1's `μ̄ = μ`), and satisfies the clipping
identity `avg (avg A h n) h (n+1) = avg A h n` (Post 7 §2.9); plus the junk-free form of the finite
conditional expectation and the **regrouping identity** behind the tower property.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- Supporting lemma `FinDist.ext` (two finite distributions with the same weights are equal).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.FinDist.ext {X : Type} [Fintype X] {μ ν : FinDist X}
    (h : ∀ x, μ.w x = ν.w x) : μ = ν := by
  cases μ; cases ν
  simp only [FinDist.mk.injEq]
  exact funext h

/-- Supporting lemma `condExpJunk_eq_div` (with junk `0` and non-negative weights the conditional
expectation is literally the quotient, since `x / 0 = 0` in Lean and a null event carries no mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.condExpJunk_eq_div {X : Type} {w f : X → ℝ}
    (E : Finset X) :
    condExpJunk w f E 0 = (∑ x ∈ E, w x * f x) / mass w E := by
  unfold condExpJunk
  split_ifs with h
  · rw [h, div_zero]
  · rfl

/-- Supporting lemma `sum_mul_eq_zero_of_mass_eq_zero` (a null event under non-negative weights
has every weight zero, so every weighted sum over it vanishes).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.weight_eq_zero_of_mass_eq_zero {X : Type} {w : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) {E : Finset X} (h : mass w E = 0) {x : X} (hx : x ∈ E) : w x = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hw y).1 h x hx
  exact this

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-! ### Atoms as an equivalence -/

/-- Supporting lemma `atomEq_refl`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_refl (n : ℕ) (ω : Ω) : S.AtomEq n ω ω := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Supporting lemma `atomEq_symm`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_symm {n : ℕ} {ω ω' : Ω} (h : S.AtomEq n ω ω') : S.AtomEq n ω' ω :=
  ⟨fun i hi => (h.1 i hi).symm, fun i hi => (h.2 i hi).symm⟩

/-- Supporting lemma `atomEq_trans`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_trans {n : ℕ} {ω ω' ω'' : Ω} (h : S.AtomEq n ω ω') (h' : S.AtomEq n ω' ω'') :
    S.AtomEq n ω ω'' :=
  ⟨fun i hi => (h.1 i hi).trans (h'.1 i hi), fun i hi => (h.2 i hi).trans (h'.2 i hi)⟩

/-- Supporting lemma `atomEq_mono` (coarser times are implied by finer ones).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_mono {m n : ℕ} (hmn : m ≤ n) {ω ω' : Ω} (h : S.AtomEq n ω ω') : S.AtomEq m ω ω' :=
  ⟨fun i hi => h.1 i (lt_of_lt_of_le hi hmn), fun i hi => h.2 i (le_trans hi hmn)⟩

/-- Supporting lemma `mem_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_atom {n : ℕ} {ω ω' : Ω} : ω' ∈ S.atom n ω ↔ S.AtomEq n ω ω' := by
  simp [atom]

/-- Supporting lemma `self_mem_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem self_mem_atom (n : ℕ) (ω : Ω) : ω ∈ S.atom n ω := S.mem_atom.2 (S.atomEq_refl n ω)

/-- Supporting lemma `atom_eq_of_atomEq` (the atom is a class of the equivalence).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom_eq_of_atomEq {n : ℕ} {ω ω' : Ω} (h : S.AtomEq n ω ω') : S.atom n ω = S.atom n ω' := by
  ext ω''
  simp only [mem_atom]
  exact ⟨fun h' => S.atomEq_trans (S.atomEq_symm h) h', fun h' => S.atomEq_trans h h'⟩

/-- Supporting lemma `atom_subset_of_le` (later atoms refine earlier ones).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom_subset_of_le {m n : ℕ} (hmn : m ≤ n) (ω : Ω) : S.atom n ω ⊆ S.atom m ω := by
  intro ω' hω'
  rw [mem_atom] at hω' ⊢
  exact S.atomEq_mono hmn hω'

/-- Supporting lemma `mass_atom_pos` (the atom of a positive-mass world is positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom_pos {n : ℕ} {ω : Ω} (hω : 0 < S.ℙ.w ω) : 0 < mass S.ℙ.w (S.atom n ω) :=
  mass_pos_of_mem S.ℙ.nonneg (S.self_mem_atom n ω) hω

/-- Supporting lemma `mass_atom_inter_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom_inter_pos {n : ℕ} {ω : Ω} (hω : 0 < S.ℙ.w ω) {E : Finset Ω} (hE : ω ∈ E) :
    0 < mass S.ℙ.w (S.atom n ω ∩ E) :=
  mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨S.self_mem_atom n ω, hE⟩) hω

/-! ### Measurability of the time-`n` quantities -/

/-- Supporting lemma `pr_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_measAt (w : Ω → ℝ) (n : ℕ) (F : Finset Ω) : S.MeasAt n (S.pr w n F) := by
  intro ω ω' h
  simp only [pr, S.atom_eq_of_atomEq h]

/-- Supporting lemma `cexp_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_measAt (w : Ω → ℝ) (n : ℕ) (E : Finset Ω) (f : Ω → ℝ) :
    S.MeasAt n (S.cexp w n E f) := by
  intro ω ω' h
  simp only [cexp, S.atom_eq_of_atomEq h]

/-- Supporting lemma `IP_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IP_measAt (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (o : O) : S.MeasAt n (S.IP n A h o) := by
  intro ω ω' hω
  simp only [IP]
  congr 1
  funext ε
  exact S.pr_measAt _ n _ ω ω' hω

/-- Supporting lemma `IEo_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IEo_measAt (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (o : O) :
    S.MeasAt n (S.IEo n A h o) := by
  intro ω ω' hω
  simp only [IEo]
  congr 1
  funext ε
  exact S.cexp_measAt _ n _ _ ω ω' hω

/-- Supporting lemma `IE_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IE_measAt (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) : S.MeasAt n (S.IE n A h) := by
  intro ω ω' hω
  simp only [IE]
  congr 1
  funext ε
  exact S.cexp_measAt _ n _ _ ω ω' hω

/-! ### Reaching `h`, the next observation, the states along `h` -/

/-- Supporting lemma `mem_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_reach {h : Node O N} {ω : Ω} : ω ∈ S.reach h ↔ LeafExt h (S.obs ω) := by
  simp [reach]

/-- Supporting lemma `mem_nextObs` (for `n < N`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs {n : ℕ} (hn : n < N) {o : O} {ω : Ω} :
    ω ∈ S.nextObs n o ↔ S.obs ω ⟨n, hn⟩ = o := by
  simp [nextObs, hn]

/-- Supporting lemma `obs_eq_of_reach` (a world reaching `h` carries `h`'s observations).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem obs_eq_of_reach {h : Node O N} {ω : Ω} (hω : ω ∈ S.reach h) (i : Fin N)
    (hi : i.val < h.1.val) : S.obs ω i = h.2 ⟨i.val, hi⟩ := by
  rw [mem_reach] at hω
  exact LeafExt.apply_eq hω i hi

/-- Supporting lemma `reach_subset_nextObs` (reaching `h` forces the observation `h_{n+1}` at `n < |h|`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach_subset_nextObs {h : Node O N} {n : ℕ} (hn : n < h.1.val) :
    S.reach h ⊆ S.nextObs n (h.2 ⟨n, hn⟩) := by
  intro ω hω
  have hnN : n < N := lt_trans hn h.1.isLt
  rw [S.mem_nextObs hnN]
  exact S.obs_eq_of_reach hω ⟨n, hnN⟩ hn

/-- Supporting lemma `not_reach_of_nextObs_ne` (**fast feedback**, Post 8: a world whose observation
at time `n < |h|` is not `h_{n+1}` does not reach `h`, and neither does anything in its later atoms).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof ("h_{n+1} failing to happen mandates that h doesn't happen")
Kind: L
Fidelity: exact
Hyps: none -/
theorem not_reach_of_nextObs_ne {h : Node O N} {n : ℕ} (hn : n < h.1.val) {o : O}
    (ho : o ≠ h.2 ⟨n, hn⟩) {ω : Ω} (hω : ω ∈ S.nextObs n o) : ω ∉ S.reach h := by
  intro hr
  have hnN : n < N := lt_trans hn h.1.isLt
  rw [S.mem_nextObs hnN] at hω
  exact ho (hω ▸ S.obs_eq_of_reach hr ⟨n, hnN⟩ hn)

/-- Supporting lemma `nextObs_eq_of_atomEq` (the time-`n` observation is `𝔽_{n+1}`-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs_iff_of_atomEq {n : ℕ} {ω ω' : Ω} (h : S.AtomEq (n + 1) ω ω') (o : O) :
    ω ∈ S.nextObs n o ↔ ω' ∈ S.nextObs n o := by
  by_cases hn : n < N
  · rw [S.mem_nextObs hn, S.mem_nextObs hn, h.1 ⟨n, hn⟩ (Nat.lt_succ_self n)]
  · simp [nextObs, hn]

/-- Supporting lemma `statesAlong_eq_of_atomEq` (the states along `h` are `𝔽_{|h|}`-measurable;
more generally two worlds in one time-`n` atom agree on the states along `h` at indices `≤ n`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem statesAlong_apply_eq_of_atomEq {n : ℕ} {ω ω' : Ω} (hω : S.AtomEq n ω ω') (h : Node O N)
    (i : Fin (h.1.val + 1)) (hi : i.val ≤ n) : S.statesAlong ω h i = S.statesAlong ω' h i :=
  hω.2 _ hi

/-- Supporting lemma `statesAlong_eq_of_atomEq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem statesAlong_eq_of_atomEq {n : ℕ} {ω ω' : Ω} (hω : S.AtomEq n ω ω') (h : Node O N)
    (hn : h.1.val ≤ n) : S.statesAlong ω h = S.statesAlong ω' h :=
  funext fun i => S.statesAlong_apply_eq_of_atomEq hω h i (by have := i.isLt; omega)

/-- Supporting lemma `play_eq_of_atomEq` (`A(h, S̄_h)` is `𝔽_{|h|}`-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_eq_of_atomEq {n : ℕ} {ω ω' : Ω} (hω : S.AtomEq n ω ω') (A : Alg O Act Ξ N)
    (h : Node O N) (hn : h.1.val ≤ n) : S.play A h ω = S.play A h ω' := by
  simp only [play, S.statesAlong_eq_of_atomEq hω h hn]

/-! ### The averaged algorithm -/

/-- Supporting lemma `mem_avgEvent`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_avgEvent {h : Node O N} {n : ℕ} {s : Fin (h.1.val + 1) → Ξ} {ω' : Ω} :
    ω' ∈ S.avgEvent h n s ↔
      (∀ i : Fin (N + 1), i.val ≤ n → ∀ hi : i.val < h.1.val + 1, S.states ω' i = s ⟨i.val, hi⟩) ∧
        ω' ∈ S.reach h := by
  simp [avgEvent]

/-- Supporting lemma `avgEvent_eq` (at a world reaching `h`, for `n ≤ |h|`, the averaging event is
the time-`n` atom intersected with `reach h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avgEvent_eq {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω} (hω : ω ∈ S.reach h) :
    S.avgEvent h n (S.statesAlong ω h) = S.atom n ω ∩ S.reach h := by
  ext ω'
  rw [S.mem_avgEvent, Finset.mem_inter, S.mem_atom]
  constructor
  · rintro ⟨hs, hr⟩
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, hr⟩
    · have hi' : i.val < h.1.val := lt_of_lt_of_le hi hn
      rw [S.obs_eq_of_reach hω i hi', S.obs_eq_of_reach hr i hi']
    · have hi' : i.val < h.1.val + 1 := by omega
      rw [hs i hi hi']
      simp only [statesAlong]
      congr 1
  · rintro ⟨⟨_, hs⟩, hr⟩
    refine ⟨fun i hi hi' => ?_, hr⟩
    rw [← hs i hi]
    simp only [statesAlong]
    congr 1

/-- Supporting lemma `avgEvent_congr` (the averaging event reads `s` at indices `≤ n` only).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avgEvent_congr {h : Node O N} {n : ℕ} {s s' : Fin (h.1.val + 1) → Ξ}
    (hs : ∀ i : Fin (h.1.val + 1), i.val ≤ n → s i = s' i) : S.avgEvent h n s = S.avgEvent h n s' := by
  ext ω'
  rw [S.mem_avgEvent, S.mem_avgEvent]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi hi' => (h1 i hi hi').trans (hs ⟨i.val, hi'⟩ hi), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi hi' => (h1 i hi hi').trans (hs ⟨i.val, hi'⟩ hi).symm, h2⟩

/-- Supporting lemma `avgDist_w_of_pos` (on a positive averaging event the averaged action
distribution is the conditional expectation of `A(h, S̄_h)(a)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avgDist_w_of_pos {A : Alg O Act Ξ N} {h : Node O N} {n : ℕ} {s : Fin (h.1.val + 1) → Ξ}
    (hpos : 0 < mass S.ℙ.w (S.avgEvent h n s)) (a : Act) :
    (S.avgDist A h n s).w a =
      condExpJunk S.ℙ.w (fun ω' => (S.play A h ω').w a) (S.avgEvent h n s) 0 := by
  unfold avgDist
  rw [dif_neg hpos.ne']

/-- Supporting lemma `avgDist_of_null`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avgDist_of_null {A : Alg O Act Ξ N} {h : Node O N} {n : ℕ} {s : Fin (h.1.val + 1) → Ξ}
    (hE : mass S.ℙ.w (S.avgEvent h n s) = 0) : S.avgDist A h n s = A h s := by
  unfold avgDist
  rw [dif_pos hE]

/-- Supporting lemma `avg_apply_self` (`Ā_{h,n}` at `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem avg_apply_self (A : Alg O Act Ξ N) (h : Node O N) (n : ℕ)
    (s : Fin (h.1.val + 1) → Ξ) : S.avg A h n h s = S.avgDist A h n s := by
  simp [avg]

/-- Supporting lemma `avg_apply_ne` (`Ā_{h,n}` elsewhere is `A`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avg_apply_ne (A : Alg O Act Ξ N) {h m : Node O N} (hm : m ≠ h) (n : ℕ)
    (s : Fin (m.1.val + 1) → Ξ) : S.avg A h n m s = A m s := by
  simp [avg, hm]

/-- Supporting lemma `play_avg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_avg (A : Alg O Act Ξ N) (h : Node O N) (n : ℕ) (ω : Ω) :
    S.play (S.avg A h n) h ω = S.avgDist A h n (S.statesAlong ω h) := by
  simp [play]

/-- **`Ā_{h,n}` is a time-`n` precommitment at `h`**: its action at `h` is constant on every time-`n`
atom whose averaging event is positive (in particular on the atom of any positive-mass world
reaching `h`, `avg_constOnAtom`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 ("on any extension of h₁:ₙ, just plays a with ℙ_{h₁:ₙ}(…) probability")
Kind: L
Fidelity: exact
Hyps: none -/
theorem play_avg_eq_of_atomEq (A : Alg O Act Ξ N) (h : Node O N) {n : ℕ} {ω ω' : Ω}
    (hpos : 0 < mass S.ℙ.w (S.avgEvent h n (S.statesAlong ω h))) (hω : S.AtomEq n ω ω') :
    S.play (S.avg A h n) h ω' = S.play (S.avg A h n) h ω := by
  rw [S.play_avg, S.play_avg]
  have hE : S.avgEvent h n (S.statesAlong ω' h) = S.avgEvent h n (S.statesAlong ω h) :=
    S.avgEvent_congr fun i hi => (S.statesAlong_apply_eq_of_atomEq hω h i hi).symm
  apply FinDist.ext
  intro a
  rw [S.avgDist_w_of_pos (hE ▸ hpos), S.avgDist_w_of_pos hpos, hE]

/-- Supporting lemma `avg_constOnAtom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avg_constOnAtom (A : Alg O Act Ξ N) {h : Node O N} {n : ℕ} {ω : Ω}
    (hpos : 0 < mass S.ℙ.w (S.avgEvent h n (S.statesAlong ω h))) :
    S.ConstOnAtom n (S.avg A h n) h ω := fun ω' hω' =>
  S.play_avg_eq_of_atomEq A h hpos (S.mem_atom.1 hω')

/-- Supporting lemma `avgEvent_pos` (the averaging event of a positive-mass world reaching `h` is
positive, for `n ≤ |h|`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem avgEvent_pos {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω} (hω : 0 < S.ℙ.w ω)
    (hr : ω ∈ S.reach h) : 0 < mass S.ℙ.w (S.avgEvent h n (S.statesAlong ω h)) := by
  rw [S.avgEvent_eq hn hr]
  exact S.mass_atom_inter_pos hω hr

/-- **At the horizon the average is the algorithm itself**: `Ā_{h,|h|}(h, S̄_h) = A(h, S̄_h)` at every
positive-mass world reaching `h` (the time-`|h|` atom determines `S̄_h`). Theorem 1's base case.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof (base case `n = |h|`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem play_avg_horizon (A : Alg O Act Ξ N) {h : Node O N} {ω : Ω} (hω : 0 < S.ℙ.w ω)
    (hr : ω ∈ S.reach h) : S.play (S.avg A h h.1.val) h ω = S.play A h ω := by
  rw [S.play_avg]
  have hpos := S.avgEvent_pos le_rfl hω hr
  apply FinDist.ext
  intro a
  rw [S.avgDist_w_of_pos hpos]
  refine condExpJunk_const_on (fun ω' hω' => ?_) hpos
  rw [S.avgEvent_eq le_rfl hr, Finset.mem_inter, S.mem_atom] at hω'
  rw [S.play_eq_of_atomEq hω'.1 A h le_rfl]

/-- **Post 8 Lemma 1's `μ̄_{h,n} = μ`**: averaging a constant algorithm returns it.
Source: `references/udt101/08-actual-algorithm.md` Lemma 1 (udt-rep-081)
Kind: L
Fidelity: exact
Hyps: none -/
theorem avg_ofDist (μ : FinDist Act) (h : Node O N) (n : ℕ) :
    S.avg (ofDist μ) h n = (ofDist μ : Alg O Act Ξ N) := by
  funext m s
  by_cases hm : m = h
  · subst hm
    rw [S.avg_apply_self]
    by_cases hE : mass S.ℙ.w (S.avgEvent m n s) = 0
    · rw [S.avgDist_of_null hE]
    · have hpos : 0 < mass S.ℙ.w (S.avgEvent m n s) :=
        lt_of_le_of_ne (mass_nonneg S.ℙ.nonneg _) (Ne.symm hE)
      apply FinDist.ext
      intro a
      rw [S.avgDist_w_of_pos hpos]
      exact condExpJunk_const_on (fun _ _ => rfl) hpos
  · rw [S.avg_apply_ne _ hm]

/-- **The clipping identity** (Post 7 §2.9): `(Ā_{h,n})‾_{h,n+1} = Ā_{h,n}` — averaging the average
again at the next time changes nothing, which is why the recursive expansion of Theorem 1 is
polynomial-sized rather than exponential.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.9 (udt-rep-085)
Kind: L
Fidelity: exact (holds for every `n`, no positivity needed)
Hyps: none -/
theorem avg_avg (A : Alg O Act Ξ N) (h : Node O N) (n : ℕ) :
    S.avg (S.avg A h n) h (n + 1) = S.avg A h n := by
  funext m s
  by_cases hm : m = h
  · subst hm
    rw [S.avg_apply_self, S.avg_apply_self]
    by_cases hE' : mass S.ℙ.w (S.avgEvent m (n + 1) s) = 0
    · rw [S.avgDist_of_null hE', S.avg_apply_self]
    · have hpos' : 0 < mass S.ℙ.w (S.avgEvent m (n + 1) s) :=
        lt_of_le_of_ne (mass_nonneg S.ℙ.nonneg _) (Ne.symm hE')
      -- the coarser averaging event contains the finer one, hence is positive too
      have hsub : S.avgEvent m (n + 1) s ⊆ S.avgEvent m n s := by
        intro ω' hω'
        rw [S.mem_avgEvent] at hω' ⊢
        exact ⟨fun i hi hi' => hω'.1 i (Nat.le_succ_of_le hi) hi', hω'.2⟩
      have hpos : 0 < mass S.ℙ.w (S.avgEvent m n s) :=
        lt_of_lt_of_le hpos' (Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω'' _ _ => S.ℙ.nonneg ω'')
      apply FinDist.ext
      intro a
      rw [S.avgDist_w_of_pos hpos']
      refine condExpJunk_const_on (fun ω' hω' => ?_) hpos'
      rw [S.play_avg]
      have hE : S.avgEvent m n (S.statesAlong ω' m) = S.avgEvent m n s := by
        rw [S.mem_avgEvent] at hω'
        refine S.avgEvent_congr fun i hi => ?_
        simp only [statesAlong]
        exact hω'.1 _ (Nat.le_succ_of_le hi) i.isLt
      rw [S.avgDist_w_of_pos (hE ▸ hpos), S.avgDist_w_of_pos hpos, hE]
  · rw [S.avg_apply_ne _ hm, S.avg_apply_ne _ hm]

/-! ### The finite conditional expectation: junk-free form, linearity, regrouping -/

/-- Supporting lemma `cexp_eq_div` (junk-free form under the prior).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_eq_div (n : ℕ) (E : Finset Ω) (f : Ω → ℝ) (ω : Ω) :
    S.cexp S.ℙ.w n E f ω = (∑ ω' ∈ S.atom n ω ∩ E, S.ℙ.w ω' * f ω') / mass S.ℙ.w (S.atom n ω ∩ E) :=
  condExpJunk_eq_div _

/-- Supporting lemma `pr_eq_div` (junk-free form under the prior).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_eq_div (n : ℕ) (F : Finset Ω) (ω : Ω) :
    S.pr S.ℙ.w n F ω = mass S.ℙ.w (F ∩ S.atom n ω) / mass S.ℙ.w (S.atom n ω) := by
  unfold pr condProbJunk
  split_ifs with h
  · rw [h, div_zero]
  · rfl

/-- Supporting lemma `cexp_const_on`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_const_on {n : ℕ} {E : Finset Ω} {f : Ω → ℝ} {ω : Ω} {c : ℝ}
    (hpos : 0 < mass S.ℙ.w (S.atom n ω ∩ E)) (hc : ∀ ω' ∈ S.atom n ω ∩ E, f ω' = c) :
    S.cexp S.ℙ.w n E f ω = c :=
  condExpJunk_const_on hc hpos

/-- Supporting lemma `cexp_sum` (linearity over a finite sum of integrands, positive event).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_sum {n : ℕ} {E : Finset Ω} {ω : Ω} (hpos : 0 < mass S.ℙ.w (S.atom n ω ∩ E))
    {ι : Type} (s : Finset ι) (g : ι → Ω → ℝ) :
    ∑ i ∈ s, S.cexp S.ℙ.w n E (g i) ω = S.cexp S.ℙ.w n E (fun ω' => ∑ i ∈ s, g i ω') ω :=
  condExpJunk_sum hpos s g

/-- Supporting lemma `cexp_const_mul` (pulling a constant out; holds with junk `0` as well).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_const_mul (n : ℕ) (E : Finset Ω) (c : ℝ) (f : Ω → ℝ) (ω : Ω) :
    S.cexp S.ℙ.w n E (fun ω' => c * f ω') ω = c * S.cexp S.ℙ.w n E f ω := by
  simp only [S.cexp_eq_div]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun ω' _ => by ring

/-- Supporting lemma `cexp_sub` (holds with junk `0` as well).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_sub (n : ℕ) (E : Finset Ω) (f g : Ω → ℝ) (ω : Ω) :
    S.cexp S.ℙ.w n E (fun ω' => f ω' - g ω') ω = S.cexp S.ℙ.w n E f ω - S.cexp S.ℙ.w n E g ω := by
  simp only [S.cexp_eq_div, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- Supporting lemma `cexp_add`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_add (n : ℕ) (E : Finset Ω) (f g : Ω → ℝ) (ω : Ω) :
    S.cexp S.ℙ.w n E (fun ω' => f ω' + g ω') ω = S.cexp S.ℙ.w n E f ω + S.cexp S.ℙ.w n E g ω := by
  simp only [S.cexp_eq_div, mul_add, Finset.sum_add_distrib, add_div]

/-- Supporting lemma `cexp_congr_on` (the conditional expectation reads `f` on the event only).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_congr_on {n : ℕ} {E : Finset Ω} {f g : Ω → ℝ} {ω : Ω}
    (hfg : ∀ ω' ∈ S.atom n ω ∩ E, f ω' = g ω') : S.cexp S.ℙ.w n E f ω = S.cexp S.ℙ.w n E g ω := by
  simp only [S.cexp_eq_div]
  congr 1
  exact Finset.sum_congr rfl fun ω' hω' => by rw [hfg ω' hω']

/-- A set of worlds is **`𝔽_n`-closed** when it is a union of time-`n` atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ClosedAt (n : ℕ) (A : Finset Ω) : Prop := ∀ ω ∈ A, ∀ ω', S.AtomEq n ω ω' → ω' ∈ A

/-- Supporting lemma `closedAt_atom` (an atom at an earlier time is a union of later atoms).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem closedAt_atom {m n : ℕ} (hmn : m ≤ n) (ω : Ω) : S.ClosedAt n (S.atom m ω) := by
  intro ω' hω' ω'' h
  rw [S.mem_atom] at hω' ⊢
  exact S.atomEq_trans hω' (S.atomEq_mono hmn h)

/-- Supporting lemma `closedAt_inter`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem closedAt_inter {n : ℕ} {A B : Finset Ω} (hA : S.ClosedAt n A) (hB : S.ClosedAt n B) :
    S.ClosedAt n (A ∩ B) := by
  intro ω hω ω' h
  rw [Finset.mem_inter] at hω ⊢
  exact ⟨hA ω hω.1 ω' h, hB ω hω.2 ω' h⟩

/-- Supporting lemma `closedAt_nextObs` (the time-`n` observation is `𝔽_{n+1}`-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem closedAt_nextObs (n : ℕ) (o : O) : S.ClosedAt (n + 1) (S.nextObs n o) := fun ω hω ω' h =>
  (S.mem_nextObs_iff_of_atomEq h o).1 hω

/-- Supporting lemma `closedAt_univ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem closedAt_univ (n : ℕ) : S.ClosedAt n (univ : Finset Ω) := fun _ _ _ _ => Finset.mem_univ _

/-- **The regrouping identity**: summing a time-`(n+1)` conditional expectation `𝔼_{n+1}[f | F]`
against the prior over an `𝔽_{n+1}`-closed set `A` collects the worlds of `A ∩ F` with the weight
`ℙ(atom_{n+1}) / ℙ(atom_{n+1} ∩ F)` of their own atoms. With `F = univ` it is the tower property;
with `F = reach h` it is the step of Post 8's Theorem 1 proof that turns
`ℙ_{h₁:ₙ}(h_{n+1}) 𝔼_{h₁:ₙ}[𝔼_{h₁:ₙ₊₁}[f | h] | h_{n+1}]` into
`𝔼_{h₁:ₙ}[(ℙ_{h₁:ₙ}(h)/ℙ_{h₁:ₙ₊₁}(h)) f | h]`. No positivity is needed: a null atom contributes
nothing on either side.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof ("collapse the two layers of expectations")
Kind: P
Fidelity: exact (finite form)
Hyps: none -/
theorem sum_cexp_regroup (n : ℕ) {A : Finset Ω} (hA : S.ClosedAt (n + 1) A) (F : Finset Ω)
    (f : Ω → ℝ) :
    ∑ ω' ∈ A, S.ℙ.w ω' * S.cexp S.ℙ.w (n + 1) F f ω' =
      ∑ ω'' ∈ A ∩ F, S.ℙ.w ω'' * f ω'' *
        (mass S.ℙ.w (S.atom (n + 1) ω'') / mass S.ℙ.w (S.atom (n + 1) ω'' ∩ F)) := by
  simp only [S.cexp_eq_div]
  -- expand the inner sums over `atom (n+1) ω' ∩ F` as sums over `A ∩ F` with an indicator
  have hinner : ∀ ω' ∈ A, S.ℙ.w ω' * ((∑ ω'' ∈ S.atom (n + 1) ω' ∩ F, S.ℙ.w ω'' * f ω'') /
      mass S.ℙ.w (S.atom (n + 1) ω' ∩ F)) =
      ∑ ω'' ∈ A ∩ F, if S.AtomEq (n + 1) ω' ω'' then
        S.ℙ.w ω' * (S.ℙ.w ω'' * f ω'' / mass S.ℙ.w (S.atom (n + 1) ω'' ∩ F)) else 0 := by
    intro ω' hω'
    have hset : (A ∩ F).filter (fun ω'' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω' ∩ F := by
      ext ω''
      simp only [Finset.mem_filter, Finset.mem_inter, S.mem_atom]
      constructor
      · rintro ⟨⟨_, hF⟩, h⟩; exact ⟨h, hF⟩
      · rintro ⟨h, hF⟩; exact ⟨⟨hA ω' hω' ω'' h, hF⟩, h⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset]
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω'' hω'' => ?_
    rw [Finset.mem_inter, S.mem_atom] at hω''
    rw [S.atom_eq_of_atomEq hω''.1, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' hω'' => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : A.filter (fun ω' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω'' := by
    ext ω'
    simp only [Finset.mem_filter, S.mem_atom]
    rw [Finset.mem_inter] at hω''
    constructor
    · rintro ⟨_, h⟩; exact S.atomEq_symm h
    · intro h; exact ⟨hA ω'' hω''.1 ω' h, S.atomEq_symm h⟩
  rw [hset, ← Finset.sum_mul]
  simp only [mass, div_eq_mul_inv]
  ring

/-- **The tower property** on a positive atom: `𝔼_n[𝔼_{n+1}[f]] = 𝔼_n[f]`.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof ("your current expectation of a quantity should equal your expectation of future-you's expectation")
Kind: P
Fidelity: exact (finite form; the post offers it as an LI-approximate identity)
Hyps: none -/
theorem cexp_cexp (n : ℕ) (f : Ω → ℝ) (ω : Ω) :
    S.cexp S.ℙ.w n univ (fun ω' => S.cexp S.ℙ.w (n + 1) univ f ω') ω = S.cexp S.ℙ.w n univ f ω := by
  rw [S.cexp_eq_div, S.cexp_eq_div]
  simp only [Finset.inter_univ]
  congr 1
  rw [S.sum_cexp_regroup n (S.closedAt_atom (Nat.le_succ n) ω) univ f]
  simp only [Finset.inter_univ]
  refine Finset.sum_congr rfl fun ω'' _ => ?_
  by_cases h0 : S.ℙ.w ω'' = 0
  · simp [h0]
  · rw [div_self (S.mass_atom_pos (lt_of_le_of_ne (S.ℙ.nonneg ω'') (Ne.symm h0))).ne', mul_one]

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
