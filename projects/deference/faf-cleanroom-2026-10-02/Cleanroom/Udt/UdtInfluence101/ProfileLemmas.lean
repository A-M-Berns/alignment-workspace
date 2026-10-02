import Cleanroom.Udt.UdtInfluence101.Profile
import Cleanroom.Udt.UdtInfluence101.Theorem1

/-!
# `Cleanroom.Udt.UdtInfluence101.ProfileLemmas`: Assumptions 3–5 in the model of record

Target T7 of [[udt-influence-101-mandate]], the `stretch` part: in the profile-predictor model,

* the environment depends on the algorithm only through its profile and its realized action at `h`
  (`F_eq`, `lawW_eq_of_not_reach`, `mass_eq_of_detBy`: the mass of an event determined by the root
  draw and the first `k ≤ |h|` letters depends on `A` only through `prof A h`);
* `prof (avg A h n) h = prof A h` (the tower property over the trace of the time-`n` atoms on
  `reach h`);
* hence **Assumption 3 holds** (`A3`), **Assumption 4 holds** (`A4`, through the decomposition
  theorem: `A` and `Ā_{h,n}` shift the law of every time-`(n+1)` atom identically), and **Assumption 5
  holds for constant algorithms** (`A5_ofDist`) and for time-`n` precommitments when no node on the
  path to `h` reads the profile at `h` (`A5_of_noSelfRead`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ W : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] [Fintype W] [DecidableEq W] {N : ℕ}

namespace PlaySpace

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (S : PlaySpace O Act Ξ N Ω)

/-- **The tower identity over the trace of the time-`n` atoms on a set `R`**:
`Σ_{ω ∈ R} ℙ(ω) 𝔼[g | atom_n(ω) ∩ R] = Σ_{ω ∈ R} ℙ(ω) g(ω)`.
Source: none: infrastructure (for `prof (avg A h n) h = prof A h`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_trace_tower (n : ℕ) (R : Finset Ω) (g : Ω → ℝ) :
    ∑ ω ∈ R, S.ℙ.w ω * condExpJunk S.ℙ.w g (S.atom n ω ∩ R) 0 = ∑ ω ∈ R, S.ℙ.w ω * g ω := by
  simp only [condExpJunk_eq_div]
  have hinner : ∀ ω ∈ R, S.ℙ.w ω * ((∑ ω'' ∈ S.atom n ω ∩ R, S.ℙ.w ω'' * g ω'') /
      mass S.ℙ.w (S.atom n ω ∩ R)) =
      ∑ ω'' ∈ R, if S.AtomEq n ω ω'' then
        S.ℙ.w ω * (S.ℙ.w ω'' * g ω'' / mass S.ℙ.w (S.atom n ω'' ∩ R)) else 0 := by
    intro ω _
    have hset : R.filter (fun ω'' => S.AtomEq n ω ω'') = S.atom n ω ∩ R := by
      ext ω''
      simp only [Finset.mem_filter, Finset.mem_inter, S.mem_atom]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω'' hω'' => ?_
    rw [Finset.mem_inter, S.mem_atom] at hω''
    rw [S.atom_eq_of_atomEq hω''.1, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' hω'' => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : R.filter (fun ω => S.AtomEq n ω ω'') = S.atom n ω'' ∩ R := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_inter, S.mem_atom]
    exact ⟨fun h => ⟨S.atomEq_symm h.2, h.1⟩, fun h => ⟨h.2, S.atomEq_symm h.1⟩⟩
  rw [hset, ← Finset.sum_mul]
  have hm : (∑ ω ∈ S.atom n ω'' ∩ R, S.ℙ.w ω) = mass S.ℙ.w (S.atom n ω'' ∩ R) := rfl
  rw [hm]
  by_cases h0 : mass S.ℙ.w (S.atom n ω'' ∩ R) = 0
  · have : S.ℙ.w ω'' = 0 := weight_eq_zero_of_mass_eq_zero S.ℙ.nonneg h0
      (Finset.mem_inter.2 ⟨S.self_mem_atom n ω'', hω''⟩)
    rw [this]; ring
  · field_simp

end PlaySpace

namespace ProfileModel

variable (M : ProfileModel O Act Ξ W N)

/-! ### The play space's projections are the model's -/

/-- Supporting lemma `toPlaySpace_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_reach (h : Node O N) : M.toPlaySpace.reach h = pReach h := rfl

/-- Supporting lemma `toPlaySpace_play`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_play (A : Alg O Act Ξ N) (h : Node O N) (ω : PWorld O Act Ξ W N) :
    M.toPlaySpace.play A h ω = A h (pStatesAlong ω h) := rfl

/-- Supporting lemma `toPlaySpace_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_w : M.toPlaySpace.ℙ.w = M.baseW := rfl

/-! ### The profile of the averaged algorithm -/

/-- Supporting lemma `prof_w_of_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_w_of_pos (A : Alg O Act Ξ N) {h : Node O N} (hpos : 0 < mass M.baseW (pReach h))
    (a : Act) :
    (M.prof A h).w a = condExpJunk M.baseW (fun ω => (A h (pStatesAlong ω h)).w a) (pReach h) 0 := by
  unfold prof
  rw [dif_neg hpos.ne']

/-- **The averaged algorithm has the profile of the algorithm** (`prof Ā_{h,n} = prof A`): what the
diffuse predictor sees of `Ā_{h,n}` is what it sees of `A`. This is the tower property over the trace
of the time-`n` atoms on `reach h`, and it is why Assumptions 3 and 4 hold in this model.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.8 ("the diffuse influence component is the same between A and Ā_{h,n} … since they have the same average behavior"); mandate T7 (`A3`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem prof_avg (A : Alg O Act Ξ N) {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) :
    M.prof (M.toPlaySpace.avg A h n) h = M.prof A h := by
  by_cases hE : mass M.baseW (pReach h) = 0
  · unfold prof; rw [dif_pos hE, dif_pos hE]
  · have hpos : 0 < mass M.baseW (pReach h) := lt_of_le_of_ne (mass_nonneg M.baseW_nonneg _) (Ne.symm hE)
    apply FinDist.ext
    intro a
    rw [M.prof_w_of_pos _ hpos, M.prof_w_of_pos _ hpos, condExpJunk_of_pos hpos, condExpJunk_of_pos hpos]
    congr 1
    set S := M.toPlaySpace with hS
    -- rewrite the inner weights of `Ā_{h,n}` as conditional expectations over `atom n ω ∩ reach h`
    have hpt : ∀ ω ∈ pReach h, M.baseW ω * (M.toPlaySpace.avg A h n h (pStatesAlong ω h)).w a =
        S.ℙ.w ω * condExpJunk S.ℙ.w (fun ω' => (A h (pStatesAlong ω' h)).w a)
          (S.atom n ω ∩ pReach h) 0 := by
      intro ω hω
      rcases (M.baseW_nonneg ω).lt_or_eq with h0 | h0
      · have hr : ω ∈ S.reach h := hω
        exact congrArg (fun x => M.baseW ω * x) (S.play_avg_w A hn h0 hr a)
      · have hz : S.ℙ.w ω = 0 := h0.symm
        rw [hz, ← h0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hpt, S.sum_trace_tower n (pReach h)]
    rfl

/-! ### The environment reads the algorithm through its profile and its action at `h` only -/

/-- Supporting lemma `F_eq` (two algorithms with the same profile at `h`, agreeing at `h` on the
state prefix if the node is `h`, give the same step factor).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_eq {A A' : Alg O Act Ξ N} {h : Node O N} (hprof : M.prof A h = M.prof A' h) (ε : ℝ)
    (r : W × Ξ) (m : Node (Letter O Act Ξ) N)
    (hA : oNode m = h → A (oNode m) (statePre r.2 m) = A' (oNode m) (statePre r.2 m))
    (ℓ : Letter O Act Ξ) : M.F A h ε r m ℓ = M.F A' h ε r m ℓ := by
  unfold F algW profW
  rw [hprof]
  by_cases hm : oNode m = h
  · rw [hA hm]
  · simp only [hm, if_false]

/-- Supporting lemma `oNode_prefixOf_eq` (a letter-prefix whose observation node is `h` witnesses
that the world reaches `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach_of_oNode_prefixOf_eq {ω : PWorld O Act Ξ W N} {k : Fin N} {h : Node O N}
    (heq : oNode (prefixOf ω.2 k) = h) : ω ∈ pReach h := by
  unfold pReach
  rw [mem_event]
  unfold oNode at heq
  obtain ⟨hk, hb⟩ := Sigma.mk.inj_iff.1 heq
  subst hk
  have hb' := eq_of_heq hb
  exact hb'

/-- **Off the branch of `h`, the ε-law depends on the algorithm only through its profile** (M2).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (the off-branch clauses)
Kind: L
Fidelity: exact
Hyps: none -/
theorem lawW_eq_of_not_reach {A A' : Alg O Act Ξ N} {h : Node O N} (hprof : M.prof A h = M.prof A' h)
    (ε : ℝ) {ω : PWorld O Act Ξ W N} (hω : ω ∉ pReach h) : M.lawW A h ε ω = M.lawW A' h ε ω := by
  unfold lawW pathLaw
  congr 1
  refine Finset.prod_congr rfl fun k _ => M.F_eq hprof ε ω.1 _ (fun heq => ?_) _
  exact absurd (reach_of_oNode_prefixOf_eq heq) hω

/-- A set of worlds is **determined by the root draw and the first `k` letters**.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def DetBy (k : ℕ) (hk : k ≤ N) (E : Finset (PWorld O Act Ξ W N)) : Prop :=
  ∀ ω ∈ E, ∀ ω' : PWorld O Act Ξ W N, ω'.1 = ω.1 → prefixOf' ω'.2 k hk = prefixOf' ω.2 k hk → ω' ∈ E

/-- Supporting lemma `apply_eq_of_prefixOf'_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.apply_eq_of_prefixOf'_eq {X : Type} {n k : ℕ} (hk : k ≤ n)
    {l l' : Leaf X n} (hp : prefixOf' l k hk = prefixOf' l' k hk) {j : Fin n} (hj : j.val < k) :
    l j = l' j := by
  have := congrFun hp ⟨j.val, hj⟩
  simpa [prefixOf'] using this

/-- Supporting lemma `prefixOf_eq_of_prefixOf'_eq_lt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.prefixOf_eq_of_prefixOf'_eq_lt {X : Type} {n k : ℕ}
    (hk : k ≤ n) {l l' : Leaf X n} (hp : prefixOf' l k hk = prefixOf' l' k hk) {j : Fin n}
    (hj : j.val < k) : prefixOf l j = prefixOf l' j := by
  unfold prefixOf
  congr 1
  funext i
  exact apply_eq_of_prefixOf'_eq hk hp (by simp; omega)

/-- Supporting lemma `prefixLaw_congr` (the prefix law reads the path on its first `k` letters only).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.prefixLaw_congr {X : Type} {n k : ℕ} (hk : k ≤ n)
    (F : Node X n → X → ℝ) {l l' : Leaf X n} (hp : prefixOf' l k hk = prefixOf' l' k hk) :
    prefixLaw F k l = prefixLaw F k l' := by
  unfold prefixLaw
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
  rw [prefixOf_eq_of_prefixOf'_eq_lt hk hp hj, apply_eq_of_prefixOf'_eq hk hp hj]

/-- **Masses of early events depend on the algorithm only through its profile** (M1): if `E` is
determined by the root draw and the first `k` letters, and two ε-play kernels agree on the first `k`
steps of every world of `E`, then `E` has the same mass under both ε-laws. (The later steps are
marginalized out: every row of the kernel sums to one.)
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3; mandate T7 ("the action factor at `h` telescopes")
Kind: P
Fidelity: exact
Hyps: none -/
theorem mass_eq_of_detBy {k : ℕ} (hk : k ≤ N) {E : Finset (PWorld O Act Ξ W N)}
    (hE : DetBy k hk E) (A A' : Alg O Act Ξ N) (h : Node O N) (ε : ℝ)
    (hF : ∀ ω ∈ E, ∀ j : Fin N, j.val < k →
      M.F A h ε ω.1 (prefixOf ω.2 j) (ω.2 j) = M.F A' h ε ω.1 (prefixOf ω.2 j) (ω.2 j)) :
    mass (M.lawW A h ε) E = mass (M.lawW A' h ε) E := by
  unfold mass
  rw [← Finset.sum_fiberwise E (fun ω => (ω.1, prefixOf' ω.2 k hk)) (M.lawW A h ε),
    ← Finset.sum_fiberwise E (fun ω => (ω.1, prefixOf' ω.2 k hk)) (M.lawW A' h ε)]
  refine Finset.sum_congr rfl fun rp _ => ?_
  obtain ⟨r, p⟩ := rp
  by_cases hne : (E.filter (fun ω => (ω.1, prefixOf' ω.2 k hk) = (r, p))).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    rw [Finset.mem_filter] at hω₀
    obtain ⟨hω₀E, hω₀rp⟩ := hω₀
    obtain ⟨hr1, hr2⟩ := Prod.mk.inj hω₀rp
    have hfib : E.filter (fun ω => (ω.1, prefixOf' ω.2 k hk) = (r, p)) =
        {r} ×ˢ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
        true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨hE ω₀ hω₀E ω (h1.trans hr1.symm) (h2.trans hr2.symm), h1, h2⟩
    rw [hfib, Finset.sum_product, Finset.sum_singleton, Finset.sum_product, Finset.sum_singleton]
    -- the common prefix factor
    have hpre : ∀ l ∈ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p),
        prefixLaw (M.F A h ε r) k l = prefixLaw (M.F A' h ε r) k ω₀.2 ∧
        prefixLaw (M.F A' h ε r) k l = prefixLaw (M.F A' h ε r) k ω₀.2 := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      have hp : prefixOf' l k hk = prefixOf' ω₀.2 k hk := hl.trans hr2.symm
      refine ⟨?_, prefixLaw_congr hk _ hp⟩
      rw [prefixLaw_congr hk _ hp]
      unfold prefixLaw
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      rw [← hr1]
      exact hF ω₀ hω₀E j hj
    have hsum := sum_suffixLaw_of_rowSum (M.F_rowSum A h ε r) (N - k) k (by omega) p
    have hsum' := sum_suffixLaw_of_rowSum (M.F_rowSum A' h ε r) (N - k) k (by omega) p
    simp only [lawW, pathLaw_eq_suffix_mul_prefix _ k]
    calc ∑ l ∈ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p),
          M.root.w r * (suffixLaw (M.F A h ε r) k l * prefixLaw (M.F A h ε r) k l)
        = ∑ l ∈ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p),
          (M.root.w r * prefixLaw (M.F A' h ε r) k ω₀.2) * suffixLaw (M.F A h ε r) k l := by
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [(hpre l hl).1]; ring
      _ = (M.root.w r * prefixLaw (M.F A' h ε r) k ω₀.2) * 1 := by
          rw [← Finset.mul_sum, hsum]
      _ = ∑ l ∈ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p),
          (M.root.w r * prefixLaw (M.F A' h ε r) k ω₀.2) * suffixLaw (M.F A' h ε r) k l := by
          rw [← Finset.mul_sum, hsum']
      _ = ∑ l ∈ univ.filter (fun l : Leaf (Letter O Act Ξ) N => prefixOf' l k hk = p),
          M.root.w r * (suffixLaw (M.F A' h ε r) k l * prefixLaw (M.F A' h ε r) k l) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [(hpre l hl).2]; ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, Finset.sum_empty]

/-! ### Assumption 3 in the model -/

/-- **At the horizon the averaged algorithm is the algorithm**: `Ā_{h,|h|} = A` as algorithms (on a
positive averaging event the average of `A(h, S̄_h)` over worlds with the given `S̄_h` is `A(h, S̄_h)`;
on a null one the junk value is `A(h, s)` by definition).
Source: `references/udt101/06-basics-of-algorithm.md` §1.3 (`n = |h|`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.PlaySpace.avg_horizon_eq {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (S : PlaySpace O Act Ξ N Ω) (A : Alg O Act Ξ N) (h : Node O N) :
    S.avg A h h.1.val = A := by
  funext m s
  by_cases hm : m = h
  · subst hm
    rw [S.avg_apply_self]
    by_cases hE : mass S.ℙ.w (S.avgEvent m m.1.val s) = 0
    · exact S.avgDist_of_null hE
    · have hpos : 0 < mass S.ℙ.w (S.avgEvent m m.1.val s) :=
        lt_of_le_of_ne (mass_nonneg S.ℙ.nonneg _) (Ne.symm hE)
      apply FinDist.ext
      intro a
      rw [S.avgDist_w_of_pos hpos]
      refine condExpJunk_const_on (fun ω' hω' => ?_) hpos
      rw [S.mem_avgEvent] at hω'
      have hs : S.statesAlong ω' m = s := by
        funext i
        have := hω'.1 ⟨i.val, by have := i.isLt; have := m.1.isLt; omega⟩ (by simp; omega) i.isLt
        exact this
      simp [PlaySpace.play, hs]
  · exact S.avg_apply_ne A hm _ _

/-- Supporting lemma `depth_ne_of_oNode_eq` (a letter-prefix of depth `< |h|` is not at `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem oNode_prefixOf_ne_of_lt {ω : PWorld O Act Ξ W N} {j : Fin N} {h : Node O N}
    (hj : j.val < h.1.val) : oNode (prefixOf ω.2 j) ≠ h := by
  intro heq
  have := congrArg (fun x : Node O N => x.1.val) heq
  simp [oNode, prefixOf] at this
  omega

/-- Supporting lemma `detBy_atom` (a time-`n` atom is determined by the root draw and the first `n`
letters, hence by the first `k ≥ n`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem detBy_atom {n k : ℕ} (hnk : n ≤ k) (hk : k ≤ N) (ω : PWorld O Act Ξ W N) :
    DetBy k hk (M.toPlaySpace.atom n ω) := by
  intro ω₁ hω₁ ω₂ hr hp
  rw [PlaySpace.mem_atom] at hω₁ ⊢
  refine PlaySpace.atomEq_trans _ hω₁ ⟨fun i hi => ?_, fun i hi => ?_⟩
  · show pObs ω₁ i = pObs ω₂ i
    unfold pObs
    rw [apply_eq_of_prefixOf'_eq hk hp.symm (by omega)]
  · show pStates ω₁ i = pStates ω₂ i
    unfold pStates
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · simp [hr]
    · simp only [Fin.cases_succ]
      rw [apply_eq_of_prefixOf'_eq hk hp.symm (by simp at hj ⊢; omega)]

/-- Supporting lemma `detBy_nextObs`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem detBy_nextObs {n : ℕ} (hn : n + 1 ≤ N) (o : O) :
    DetBy (n + 1) hn (M.toPlaySpace.nextObs n o) := by
  intro ω₁ hω₁ ω₂ _ hp
  have hnN : n < N := by omega
  rw [PlaySpace.mem_nextObs _ hnN] at hω₁ ⊢
  show pObs ω₂ ⟨n, hnN⟩ = o
  rw [← hω₁]
  unfold pObs
  rw [apply_eq_of_prefixOf'_eq hn hp (by simp)]
  rfl

/-- Supporting lemma `detBy_inter`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem detBy_inter {k : ℕ} {hk : k ≤ N} {E E' : Finset (PWorld O Act Ξ W N)} (h1 : DetBy k hk E)
    (h2 : DetBy k hk E') : DetBy k hk (E ∩ E') := by
  intro ω hω ω' hr hp
  rw [Finset.mem_inter] at hω ⊢
  exact ⟨h1 ω hω.1 ω' hr hp, h2 ω hω.2 ω' hr hp⟩

/-- Supporting lemma `mass_eq_of_detBy_lt` (M1 specialized: events determined by the first
`k ≤ |h|` letters have the same ε-mass under any two algorithms with the same profile at `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_of_detBy_le {k : ℕ} (hk : k ≤ N) {h : Node O N} (hkh : k ≤ h.1.val)
    {E : Finset (PWorld O Act Ξ W N)} (hE : DetBy k hk E) {A A' : Alg O Act Ξ N}
    (hprof : M.prof A h = M.prof A' h) (ε : ℝ) :
    mass (M.lawW A h ε) E = mass (M.lawW A' h ε) E :=
  M.mass_eq_of_detBy hk hE A A' h ε fun ω _ j hj =>
    M.F_eq hprof ε ω.1 _ (fun heq => absurd heq (oNode_prefixOf_ne_of_lt (by omega))) _

/-- Supporting lemma `toPlaySpace_law`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_law : M.toPlaySpace.law = M.lawW := rfl

/-- **Post 6's Assumption 3 holds in the model of record**: the environment sees the algorithm only
through its profile (which `Ā_{h,n}` shares with `A`, `prof_avg`) and through its realized action at
`h` (which, at the horizon, `Ā_{h,|h|} = A` shares too). Off the branch of `h` nothing else enters
(`lawW_eq_of_not_reach`); before the horizon the action at `h` is marginalized out
(`mass_eq_of_detBy_le`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (udt-rep-080, 086); mandate T7 (`A3`), T8(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem A3 (h : Node O N) : M.toPlaySpace.A3 h := by
  intro n hn A ω hω hr
  rcases Nat.lt_or_ge n h.1.val with hlt | hge
  · have hprof : M.prof A h = M.prof (M.toPlaySpace.avg A h n) h := (M.prof_avg A hn).symm
    have hn1 : n + 1 ≤ N := by have := h.1.isLt; omega
    refine ⟨fun o => ?_, fun o ho => ?_⟩
    · -- influence on probability: the conditional probability is the same function of `ε`
      unfold PlaySpace.IP
      congr 1
      funext ε
      unfold PlaySpace.pr condProbJunk
      rw [M.toPlaySpace_law,
        M.mass_eq_of_detBy_le hn1 (by omega) (M.detBy_atom (Nat.le_succ n) hn1 ω) hprof ε,
        M.mass_eq_of_detBy_le hn1 (by omega)
          (detBy_inter (M.detBy_nextObs hn1 o) (M.detBy_atom (Nat.le_succ n) hn1 ω)) hprof ε]
    · -- off-branch influence on conditional expected utility: pointwise equal weights
      unfold PlaySpace.IEo
      congr 1
      funext ε
      unfold PlaySpace.cexp condExpJunk mass
      rw [M.toPlaySpace_law]
      have hpt : ∀ ω' ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n o,
          M.lawW A h ε ω' = M.lawW (M.toPlaySpace.avg A h n) h ε ω' := by
        intro ω' hω'
        have hnr : ω' ∉ M.toPlaySpace.reach h :=
          M.toPlaySpace.not_reach_of_nextObs_ne hlt (ho hlt) (Finset.mem_inter.1 hω').2
        exact M.lawW_eq_of_not_reach hprof ε hnr
      have h1 : ∑ x ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n o, M.lawW A h ε x =
          ∑ x ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n o,
            M.lawW (M.toPlaySpace.avg A h n) h ε x := Finset.sum_congr rfl hpt
      have h2 : ∑ x ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n o,
          M.lawW A h ε x * M.toPlaySpace.U x =
          ∑ x ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n o,
            M.lawW (M.toPlaySpace.avg A h n) h ε x * M.toPlaySpace.U x :=
        Finset.sum_congr rfl fun x hx => by rw [hpt x hx]
      rw [h1, h2]
  · have heq : n = h.1.val := le_antisymm hn hge
    subst heq
    rw [M.toPlaySpace.avg_horizon_eq A h]
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

/-! ### Assumption 4 in the model -/

/-- Supporting lemma `sum_mul_measAt_regroup` (a sum `Σ f·g` with `g` constant on time-`(n+1)` atoms
collects `f` over each atom, weighted by the prior).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.PlaySpace.sum_mul_measAt_regroup {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (S : PlaySpace O Act Ξ N Ω) (n : ℕ) {E : Finset Ω} (hE : S.ClosedAt (n + 1) E)
    (hpos : ∀ ω' ∈ E, 0 < mass S.ℙ.w (S.atom (n + 1) ω')) {g : Ω → ℝ} (hg : S.MeasAt (n + 1) g)
    (f : Ω → ℝ) :
    ∑ ω' ∈ E, f ω' * g ω' =
      ∑ ω' ∈ E, S.ℙ.w ω' * g ω' * ((∑ ω'' ∈ S.atom (n + 1) ω', f ω'') / mass S.ℙ.w (S.atom (n + 1) ω')) := by
  have hinner : ∀ ω' ∈ E, S.ℙ.w ω' * g ω' * ((∑ ω'' ∈ S.atom (n + 1) ω', f ω'') /
      mass S.ℙ.w (S.atom (n + 1) ω')) =
      ∑ ω'' ∈ E, if S.AtomEq (n + 1) ω' ω'' then
        S.ℙ.w ω' * g ω' * (f ω'' / mass S.ℙ.w (S.atom (n + 1) ω'')) else 0 := by
    intro ω' hω'
    have hset : E.filter (fun ω'' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω' := by
      ext ω''
      simp only [Finset.mem_filter, S.mem_atom]
      exact ⟨fun h => h.2, fun h => ⟨hE ω' hω' ω'' h, h⟩⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω'' hω'' => ?_
    rw [S.mem_atom] at hω''
    rw [S.atom_eq_of_atomEq hω'', div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' hω'' => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : E.filter (fun ω' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω'' := by
    ext ω'
    simp only [Finset.mem_filter, S.mem_atom]
    exact ⟨fun h => S.atomEq_symm h.2, fun h => ⟨hE ω'' hω'' ω' h, S.atomEq_symm h⟩⟩
  rw [hset]
  have hgc : ∀ ω' ∈ S.atom (n + 1) ω'', g ω' = g ω'' := fun ω' hω' =>
    (hg ω'' ω' (S.mem_atom.1 hω')).symm
  rw [Finset.sum_congr rfl fun ω' hω' => by rw [hgc ω' hω'], ← Finset.sum_mul, ← Finset.sum_mul]
  have hm : (∑ ω' ∈ S.atom (n + 1) ω'', S.ℙ.w ω') = mass S.ℙ.w (S.atom (n + 1) ω'') := rfl
  rw [hm]
  field_simp [(hpos ω'' hω'').ne']

/-- **Post 7's Assumption 4 at `(n, ω)` from equal atom-level shifts**: if ε-playing `A` and ε-playing
`Ā_{h,n}` shift the conditional probability of every time-`(n+1)` atom below `h_{n+1}` identically,
the CEG identity holds at `(n, ω)`.
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4 and §2.8; mandate T6(a), T7
Kind: C
Fidelity: exact
Hyps: as `IEo_decomp`, plus the equal-shift hypothesis -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.PlaySpace.A4_at_of_atomShift_eq {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (S : PlaySpace O Act Ξ N Ω) (hS : S.SmoothLaw) {h : Node O N} {n : ℕ}
    (hn : n < h.1.val) {ω : Ω}
    (hE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)))
    (hatoms : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩), 0 < mass S.ℙ.w (S.atom (n + 1) ω'))
    (A : Alg O Act Ξ N)
    (hshift : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩),
      ∑ ω'' ∈ S.atom (n + 1) ω', S.dcw A h (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) ω'' =
        ∑ ω'' ∈ S.atom (n + 1) ω', S.dcw (S.avg A h n) h (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) ω'') :
    S.IEo n A h (h.2 ⟨n, hn⟩) ω - S.IEo n (S.avg A h n) h (h.2 ⟨n, hn⟩) ω =
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩))
        (fun ω' => S.IE (n + 1) A h ω' - S.IE (n + 1) (S.avg A h n) h ω') ω := by
  have hclosed : S.ClosedAt (n + 1) (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) :=
    S.closedAt_inter (S.closedAt_atom (Nat.le_succ n) ω) (S.closedAt_nextObs n _)
  rw [S.IEo_decomp hS _ hE hatoms A h, S.IEo_decomp hS _ hE hatoms (S.avg A h n) h, S.cexp_sub,
    S.sum_mul_measAt_regroup n hclosed hatoms (S.cexp_measAt S.ℙ.w (n + 1) univ S.U),
    S.sum_mul_measAt_regroup n hclosed hatoms (S.cexp_measAt S.ℙ.w (n + 1) univ S.U),
    Finset.sum_congr rfl fun ω' hω' => by rw [hshift ω' hω']]
  ring

/-- **Post 7's Assumption 4 (Conservation of Expected Gain) holds in the model of record**, given
positivity of the time-`(n+1)` atoms below `h_{n+1}`: the ε-shift of the conditional probability of
any such atom depends on the algorithm only through its profile (`mass_eq_of_detBy_le`), which
`Ā_{h,n}` shares with `A`. The source *assumes* this ("Formal Assumption 4"); here it is derived.
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4 (udt-rep-085); mandate T6(a), T7
Kind: P
Fidelity: exact
Hyps: (a) positivity of the time-`(n+1)` atoms below `h_{n+1}` along `h` (regularity, checked on the instances) -/
theorem A4 (h : Node O N)
    (hatoms : ∀ (n : ℕ) (hn : n < h.1.val) (ω : PWorld O Act Ξ W N), 0 < M.baseW ω → ω ∈ pReach h →
      ∀ ω' ∈ M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩),
        0 < mass M.baseW (M.toPlaySpace.atom (n + 1) ω')) :
    M.toPlaySpace.A4 h := by
  intro n hn A ω hω hr
  have hE : 0 < mass M.toPlaySpace.ℙ.w (M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩)) :=
    M.toPlaySpace.mass_atom_inter_pos hω (M.toPlaySpace.reach_subset_nextObs hn hr)
  have hn1 : n + 1 ≤ N := by have := h.1.isLt; omega
  have hprof : M.prof A h = M.prof (M.toPlaySpace.avg A h n) h := (M.prof_avg A hn.le).symm
  refine M.toPlaySpace.A4_at_of_atomShift_eq M.smoothLaw hn hE (hatoms n hn ω hω hr) A fun ω' hω' => ?_
  have key : ∀ A' : Alg O Act Ξ N,
      ∑ ω'' ∈ M.toPlaySpace.atom (n + 1) ω',
        M.toPlaySpace.dcw A' h (M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩)) ω'' =
      deriv (fun ε => mass (M.toPlaySpace.law A' h ε) (M.toPlaySpace.atom (n + 1) ω') /
        mass (M.toPlaySpace.law A' h ε) (M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩))) 0 := by
    intro A'
    have hd : HasDerivAt (fun ε => ∑ ω'' ∈ M.toPlaySpace.atom (n + 1) ω',
        M.toPlaySpace.law A' h ε ω'' /
          mass (M.toPlaySpace.law A' h ε) (M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩)))
        (∑ ω'' ∈ M.toPlaySpace.atom (n + 1) ω',
          M.toPlaySpace.dcw A' h (M.toPlaySpace.atom n ω ∩ M.toPlaySpace.nextObs n (h.2 ⟨n, hn⟩)) ω'') 0 := by
      apply HasDerivAt.fun_sum
      intro ω'' _
      have hc := M.toPlaySpace.hasDerivAt_condWeight M.smoothLaw A' h hE ω''
      exact hc.congr_deriv hc.deriv.symm
    rw [← hd.deriv]
    congr 1
    funext ε
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rfl
  rw [key A, key (M.toPlaySpace.avg A h n)]
  congr 1
  funext ε
  rw [M.toPlaySpace_law,
    M.mass_eq_of_detBy_le hn1 (by omega) (M.detBy_atom le_rfl hn1 ω') hprof ε,
    M.mass_eq_of_detBy_le hn1 (by omega)
      (detBy_inter (M.detBy_atom (Nat.le_succ n) hn1 ω) (M.detBy_nextObs hn1 _)) hprof ε]

end ProfileModel

end

end Cleanroom.Udt.UdtInfluence101
