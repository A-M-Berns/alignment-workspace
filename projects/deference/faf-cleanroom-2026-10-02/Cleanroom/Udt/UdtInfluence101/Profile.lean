import Cleanroom.Udt.UdtInfluence101.Conservation

/-!
# `Cleanroom.Udt.UdtInfluence101.Profile`: the profile-predictor model of record

Target T7 of [[udt-influence-101-mandate]], the construction. A world is a root draw `(w, ξ₀)` (latent
world and first unplannable state) followed by `N` letters `(a_k, o_k, ξ_{k+1})`: at step `k` the agent
acts at the plannable history `o_{<k}` knowing the states `ξ_{≤k}`, the environment draws the
observation `o_k` from a kernel that reads `w`, the history, the past actions, the current action and
**the agent's action profile at a designated node** `pn m` (the "diffuse prediction": the environment
sees only the baseline-conditional average behaviour, Post 6 §1.2), and then the next state `ξ_{k+1}`
is drawn. ε-play of `A` at `h` mixes the action at `h` (`(1−ε)·B + ε·A`) and the profile read for `h`
(`(1−ε)·π₀ h + ε·prof A h`), where `prof A h` is the conditional average of `A(h, S̄_h)` over `reach h`
under the **baseline** law (the predictor's baseline belief `π₀` is data, so nothing is circular).
Every coordinate of the ε-law is a polynomial in `ε` (a product of affine factors), so `SmoothLaw`,
hence Post 6's Assumption 1, is a theorem here (`smoothLaw`).

The observation kernel is affine in the profile by construction (`e(o | q) = Σ_{a'} q(a') · eA(a')(o)`);
`eA` constant in `a'` gives a kernel that reads no profile.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

/-- A **letter** of the model: the action taken, the observation received, the next state.
Source: mandate §3 (`Ω := W × (Fin (N+1) → Ξ) × Leaf × (Fin N → Act)`, re-encoded as a path)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Letter (O Act Ξ : Type) := Act × O × Ξ

/-- A **world** of the model: the root draw `(w, ξ₀)` and the path of `N` letters.
Source: mandate §3
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev PWorld (O Act Ξ W : Type) (N : ℕ) := (W × Ξ) × Leaf (Letter O Act Ξ) N

variable {O Act Ξ W : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] [Fintype W] [DecidableEq W] {N : ℕ}

/-- The observations along a letter-prefix.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def obsPre (m : Node (Letter O Act Ξ) N) : Fin m.1.val → O := fun i => (m.2 i).2.1

/-- The actions along a letter-prefix.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actPre (m : Node (Letter O Act Ξ) N) : Fin m.1.val → Act := fun i => (m.2 i).1

/-- The states received along a letter-prefix, starting from the root state.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def statePre (ξ₀ : Ξ) (m : Node (Letter O Act Ξ) N) : Fin (m.1.val + 1) → Ξ :=
  Fin.cases ξ₀ (fun i => (m.2 i).2.2)

/-- The plannable history (observation node) of a letter-prefix.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def oNode (m : Node (Letter O Act Ξ) N) : Node O N := ⟨m.1, obsPre m⟩

/-- The completed observation history of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pObs (ω : PWorld O Act Ξ W N) : Leaf O N := fun k => (ω.2 k).2.1

/-- The states of a world at times `0, …, N`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pStates (ω : PWorld O Act Ξ W N) : Fin (N + 1) → Ξ := Fin.cases ω.1.2 (fun k => (ω.2 k).2.2)

/-- **The profile-predictor model** (data).
Source: mandate §3 ("Model of record (`ProfileModel`)")
Kind: D
Fidelity: variant: the epistemic states' beliefs about the agent are rendered as one prior over
`(w, S̄, history, actions)` and the environment's "prediction" as the baseline-conditional action
profile at a designated node, read affinely — a modelling choice for an object the source leaves
informal, not a substitution for an FAF object
Hyps: n/a -/
structure ProfileModel (O Act Ξ W : Type) [Fintype O] [Fintype Act] [Fintype Ξ] [Fintype W]
    (N : ℕ) where
  /-- The prior on the latent world and the first state. -/
  root : FinDist (W × Ξ)
  /-- The state kernel: next state given `w`, history, states so far, current action, observation. -/
  κ : W → (k : Fin N) → (Fin k.val → O) → (Fin (k.val + 1) → Ξ) → Act → O → FinDist Ξ
  /-- The observation kernel given `w`, history, past actions, the current action and a *predicted*
  action `a'`; the environment mixes it with the profile at `pn`. -/
  eA : W → (k : Fin N) → (Fin k.val → O) → (Fin k.val → Act) → Act → Act → FinDist O
  /-- Which node's profile the environment reads at each node. -/
  pn : Node O N → Node O N
  /-- The baseline algorithm. -/
  B : Alg O Act Ξ N
  /-- The predictor's baseline belief about the agent's profile at each node. -/
  π₀ : Node O N → FinDist Act
  /-- The utility of a world. -/
  U : PWorld O Act Ξ W N → ℝ

namespace ProfileModel

variable (M : ProfileModel O Act Ξ W N)

/-- The **baseline step kernel** on letter-prefixes: action from `B`, observation from `eA` mixed by
the baseline profile `π₀ (pn m)`, next state from `κ`.
Source: mandate §3
Kind: D
Fidelity: n/a
Hyps: n/a -/
def baseF (r : W × Ξ) : Node (Letter O Act Ξ) N → Letter O Act Ξ → ℝ := fun m ℓ =>
  (M.B (oNode m) (statePre r.2 m)).w ℓ.1 *
    (∑ a', (M.π₀ (M.pn (oNode m))).w a' * (M.eA r.1 m.1 (obsPre m) (actPre m) ℓ.1 a').w ℓ.2.1) *
    (M.κ r.1 m.1 (obsPre m) (statePre r.2 m) ℓ.1 ℓ.2.1).w ℓ.2.2

/-- The **baseline weight** of a world.
Source: mandate §3
Kind: D
Fidelity: n/a
Hyps: n/a -/
def baseW (ω : PWorld O Act Ξ W N) : ℝ := M.root.w ω.1 * pathLaw (M.baseF ω.1) ω.2

/-- Supporting lemma `sum_letter` (a sum over letters as an iterated sum).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_letter (f : Letter O Act Ξ → ℝ) : ∑ ℓ, f ℓ = ∑ a, ∑ o, ∑ ξ, f (a, o, ξ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]

/-- Supporting lemma `baseF_rowStochastic`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_rowStochastic (r : W × Ξ) : RowStochastic (M.baseF r) := by
  refine ⟨fun m ℓ => ?_, fun m => ?_⟩
  · unfold baseF
    refine mul_nonneg (mul_nonneg (FinDist.nonneg _ _) (Finset.sum_nonneg fun a' _ =>
      mul_nonneg (FinDist.nonneg _ _) (FinDist.nonneg _ _))) (FinDist.nonneg _ _)
  · rw [sum_letter]
    simp only [baseF]
    calc ∑ a, ∑ o, ∑ ξ, (M.B (oNode m) (statePre r.2 m)).w a *
          (∑ a', (M.π₀ (M.pn (oNode m))).w a' * (M.eA r.1 m.1 (obsPre m) (actPre m) a a').w o) *
          (M.κ r.1 m.1 (obsPre m) (statePre r.2 m) a o).w ξ
        = ∑ a, ∑ o, (M.B (oNode m) (statePre r.2 m)).w a *
          (∑ a', (M.π₀ (M.pn (oNode m))).w a' * (M.eA r.1 m.1 (obsPre m) (actPre m) a a').w o) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun o _ => ?_
          rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
      _ = ∑ a, (M.B (oNode m) (statePre r.2 m)).w a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [← Finset.mul_sum, FinDist.sum_one, mul_one]
      _ = 1 := FinDist.sum_one _

/-- Supporting lemma `baseW_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_nonneg (ω : PWorld O Act Ξ W N) : 0 ≤ M.baseW ω :=
  mul_nonneg (M.root.nonneg _) (pathLaw_nonneg (M.baseF_rowStochastic ω.1) _)

/-- Supporting lemma `sum_root_mul_pathLaw` (summing a root-indexed path law over worlds).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_root_mul_pathLaw (F : W × Ξ → Node (Letter O Act Ξ) N → Letter O Act Ξ → ℝ)
    (hF : ∀ r, ∑ l, pathLaw (F r) l = 1) :
    ∑ ω : PWorld O Act Ξ W N, M.root.w ω.1 * pathLaw (F ω.1) ω.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hF, mul_one]
  exact M.root.sum_one

/-- Supporting lemma `baseW_sum_one`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_sum_one : ∑ ω, M.baseW ω = 1 :=
  M.sum_root_mul_pathLaw M.baseF fun r => pathLaw_sum_one (M.baseF_rowStochastic r)

/-- The baseline prior as a finite distribution.
Source: mandate §3
Kind: D
Fidelity: n/a
Hyps: n/a -/
def basePrior : FinDist (PWorld O Act Ξ W N) := ⟨M.baseW, M.baseW_nonneg, M.baseW_sum_one⟩

/-- The states received on the way to `h` (the model's `S̄_h`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pStatesAlong (ω : PWorld O Act Ξ W N) (h : Node O N) : Fin (h.1.val + 1) → Ξ :=
  fun i => pStates ω (Fin.castLE (by have := h.1.isLt; omega) i)

/-- The worlds reaching `h`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pReach (h : Node O N) : Finset (PWorld O Act Ξ W N) := event (fun ω => LeafExt h (pObs ω))

/-- **The action profile at `h`**: the baseline-conditional average of `A(h, S̄_h)` over the worlds
reaching `h` — what the diffuse predictor sees of `A`. **Junk**: when `reach h` is null under the
baseline, the predictor's baseline belief `π₀ h` is returned (disclosed; the instances have positive
`reach h`).
Source: `references/udt101/06-basics-of-algorithm.md` §1.2 ("predictors which just look at your average behavior"); mandate §3 (`prof`)
Kind: D
Fidelity: variant: see `ProfileModel`
Hyps: n/a -/
def prof (A : Alg O Act Ξ N) (h : Node O N) : FinDist Act :=
  if hE : mass M.baseW (pReach h) = 0 then M.π₀ h else
  { w := fun a => condExpJunk M.baseW (fun ω => (A h (pStatesAlong ω h)).w a) (pReach h) 0
    nonneg := fun a => by
      have hpos : 0 < mass M.baseW (pReach h) :=
        lt_of_le_of_ne (mass_nonneg M.baseW_nonneg _) (Ne.symm hE)
      exact le_condExpJunk_of_le M.baseW_nonneg hpos fun ω _ => (A h _).nonneg a
    sum_one := by
      have hpos : 0 < mass M.baseW (pReach h) :=
        lt_of_le_of_ne (mass_nonneg M.baseW_nonneg _) (Ne.symm hE)
      rw [condExpJunk_sum hpos]
      exact condExpJunk_const_on (fun ω _ => (A h _).sum_one) hpos }

/-- The action weights under ε-play of `A` at `h`: the mixture `(1−ε)·B + ε·A` at `h`, `B` elsewhere
(a signed weight for `ε ∉ [0,1]`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 ("A is ε-played at h")
Kind: D
Fidelity: exact (polynomial extension)
Hyps: n/a -/
def algW (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (m : Node O N) (s : Fin (m.1.val + 1) → Ξ)
    (a : Act) : ℝ :=
  if m = h then (1 - ε) * (M.B m s).w a + ε * (A m s).w a else (M.B m s).w a

/-- The profile weights the environment reads under ε-play of `A` at `h`: `(1−ε)·π₀ h + ε·prof A h`
at `h`, `π₀` elsewhere.
Source: mandate §3 (`law A h ε` "with the profile `(1−ε)·prof B + ε·prof A` at `h`")
Kind: D
Fidelity: exact (polynomial extension)
Hyps: n/a -/
def profW (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (m : Node O N) (a' : Act) : ℝ :=
  if m = h then (1 - ε) * (M.π₀ h).w a' + ε * (M.prof A h).w a' else (M.π₀ m).w a'

/-- The **ε-play step kernel** on letter-prefixes.
Source: mandate §3
Kind: D
Fidelity: n/a
Hyps: n/a -/
def F (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (r : W × Ξ) :
    Node (Letter O Act Ξ) N → Letter O Act Ξ → ℝ := fun m ℓ =>
  M.algW A h ε (oNode m) (statePre r.2 m) ℓ.1 *
    (∑ a', M.profW A h ε (M.pn (oNode m)) a' * (M.eA r.1 m.1 (obsPre m) (actPre m) ℓ.1 a').w ℓ.2.1) *
    (M.κ r.1 m.1 (obsPre m) (statePre r.2 m) ℓ.1 ℓ.2.1).w ℓ.2.2

/-- The **ε-law** of the model: the weight of a world when `A` is ε-played at `h`.
Source: mandate §3
Kind: D
Fidelity: exact (polynomial extension)
Hyps: n/a -/
def lawW (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (ω : PWorld O Act Ξ W N) : ℝ :=
  M.root.w ω.1 * pathLaw (M.F A h ε ω.1) ω.2

/-! ### The ε-law is a distribution for `ε ∈ [0,1]`, has mass one for every `ε`, and is the baseline at `0` -/

/-- Supporting lemma `algW_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem algW_sum (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (m : Node O N) (s : Fin (m.1.val + 1) → Ξ) :
    ∑ a, M.algW A h ε m s a = 1 := by
  unfold algW
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FinDist.sum_one, FinDist.sum_one]
    ring
  · exact FinDist.sum_one _

/-- Supporting lemma `profW_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem profW_sum (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (m : Node O N) :
    ∑ a', M.profW A h ε m a' = 1 := by
  unfold profW
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FinDist.sum_one, FinDist.sum_one]
    ring
  · exact FinDist.sum_one _

/-- Supporting lemma `F_rowSum` (every row of the ε-play kernel sums to one, for every real `ε`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_rowSum (A : Alg O Act Ξ N) (h : Node O N) (ε : ℝ) (r : W × Ξ)
    (m : Node (Letter O Act Ξ) N) : ∑ ℓ, M.F A h ε r m ℓ = 1 := by
  rw [sum_letter]
  simp only [F]
  calc ∑ a, ∑ o, ∑ ξ, M.algW A h ε (oNode m) (statePre r.2 m) a *
        (∑ a', M.profW A h ε (M.pn (oNode m)) a' * (M.eA r.1 m.1 (obsPre m) (actPre m) a a').w o) *
        (M.κ r.1 m.1 (obsPre m) (statePre r.2 m) a o).w ξ
      = ∑ a, ∑ o, M.algW A h ε (oNode m) (statePre r.2 m) a *
        (∑ a', M.profW A h ε (M.pn (oNode m)) a' * (M.eA r.1 m.1 (obsPre m) (actPre m) a a').w o) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun o _ => ?_
        rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
    _ = ∑ a, M.algW A h ε (oNode m) (statePre r.2 m) a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [← Finset.mul_sum, FinDist.sum_one, mul_one, M.profW_sum]
    _ = 1 := M.algW_sum A h ε _ _

/-- Supporting lemma `F_nonneg` (for `ε ∈ [0,1]`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_nonneg (A : Alg O Act Ξ N) (h : Node O N) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (r : W × Ξ)
    (m : Node (Letter O Act Ξ) N) (ℓ : Letter O Act Ξ) : 0 ≤ M.F A h ε r m ℓ := by
  have h1' : 0 ≤ 1 - ε := by linarith
  unfold F
  refine mul_nonneg (mul_nonneg ?_ (Finset.sum_nonneg fun a' _ => mul_nonneg ?_ (FinDist.nonneg _ _)))
    (FinDist.nonneg _ _)
  · unfold algW
    split_ifs
    · have := (M.B (oNode m) (statePre r.2 m)).nonneg ℓ.1
      have := (A (oNode m) (statePre r.2 m)).nonneg ℓ.1
      positivity
    · exact FinDist.nonneg _ _
  · unfold profW
    split_ifs
    · have := (M.π₀ h).nonneg a'
      have := (M.prof A h).nonneg a'
      positivity
    · exact FinDist.nonneg _ _

/-- Supporting lemma `algW_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem algW_zero (A : Alg O Act Ξ N) (h : Node O N) (m : Node O N) (s : Fin (m.1.val + 1) → Ξ)
    (a : Act) : M.algW A h 0 m s a = (M.B m s).w a := by
  unfold algW
  split_ifs with hm
  · subst hm; ring
  · rfl

/-- Supporting lemma `profW_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem profW_zero (A : Alg O Act Ξ N) (h : Node O N) (m : Node O N) (a' : Act) :
    M.profW A h 0 m a' = (M.π₀ m).w a' := by
  unfold profW
  split_ifs with hm
  · subst hm; ring
  · rfl

/-- Supporting lemma `F_zero` (at `ε = 0` the ε-play kernel is the baseline kernel).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_zero (A : Alg O Act Ξ N) (h : Node O N) (r : W × Ξ) : M.F A h 0 r = M.baseF r := by
  funext m ℓ
  simp only [F, baseF, M.algW_zero, M.profW_zero]

/-- Supporting lemma `sum_suffixLaw_of_rowSum` (the dependency's `Tree.sum_suffixLaw`, with only the
row-sum-one half of `RowStochastic`; needed for the signed ε-law).
Source: none: infrastructure (re-proof of `Cleanroom.Udt.UdtPolicyCalc.Tree.sum_suffixLaw`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.sum_suffixLaw_of_rowSum {X : Type} [Fintype X]
    [DecidableEq X] {n : ℕ} {F : Node X n → X → ℝ} (hF : ∀ h, ∑ o, F h o = 1) :
    ∀ (d m : ℕ) (hd : m + d = n) (p : Fin m → X),
      ∑ l ∈ univ.filter (fun l : Leaf X n => prefixOf' l m (by omega) = p), suffixLaw F m l = 1 := by
  intro d
  induction d with
  | zero =>
    intro m hd p
    have hmn : m = n := by omega
    subst hmn
    have hfilt : (univ.filter fun l : Leaf X m => prefixOf' l m (by omega) = p) = {p} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [prefixOf'_self]
    rw [hfilt, Finset.sum_singleton, suffixLaw]
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact absurd hk (by omega)
  | succ d ih =>
    intro m hd p
    have hm : m + 1 ≤ n := by omega
    calc ∑ l ∈ univ.filter (fun l : Leaf X n => prefixOf' l m (by omega) = p), suffixLaw F m l
        = ∑ l ∈ univ.filter (fun l : Leaf X n => prefixOf' l m (by omega) = p),
            F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l := by
          refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          rw [suffixLaw_succ F m hm l, prefixOf_eq_of_prefixOf' hm hl]
      _ = ∑ o, ∑ l ∈ (univ.filter (fun l : Leaf X n => prefixOf' l m (by omega) = p)).filter
            (fun l => l ⟨m, hm⟩ = o), F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l :=
          (Finset.sum_fiberwise (univ.filter (fun l : Leaf X n => prefixOf' l m (by omega) = p))
            (fun l => l ⟨m, hm⟩)
            (fun l => F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l)).symm
      _ = ∑ o, F ⟨⟨m, hm⟩, p⟩ o *
            ∑ l ∈ univ.filter (fun l : Leaf X n => prefixOf' l (m + 1) hm = Fin.snoc p o),
              suffixLaw F (m + 1) l := by
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [Finset.mul_sum, ← filter_prefix_succ m hm p o]
          refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_filter] at hl
          rw [hl.2]
      _ = ∑ o, F ⟨⟨m, hm⟩, p⟩ o * 1 := by
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [ih (m + 1) (by omega) (Fin.snoc p o)]
      _ = 1 := by
          simp only [mul_one]
          exact hF _

/-- Supporting lemma `pathLaw_sum_one_of_rowSum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtInfluence101.pathLaw_sum_one_of_rowSum {X : Type} [Fintype X]
    [DecidableEq X] {n : ℕ} {F : Node X n → X → ℝ} (hF : ∀ h, ∑ o, F h o = 1) :
    ∑ l, pathLaw F l = 1 := by
  have := sum_suffixLaw_of_rowSum hF n 0 (by omega) (Fin.elim0)
  rw [Finset.filter_true_of_mem (fun l _ => Subsingleton.elim _ _)] at this
  simpa [suffixLaw_zero] using this

/-- **The play space of the model**: baseline prior, projections, utility, and the ε-law.
Source: mandate §3, T7
Kind: D
Fidelity: see `ProfileModel`
Hyps: n/a -/
def toPlaySpace : PlaySpace O Act Ξ N (PWorld O Act Ξ W N) where
  ℙ := M.basePrior
  obs := pObs
  states := pStates
  U := M.U
  law := M.lawW
  law_zero := fun A h => by
    funext ω
    simp only [lawW, basePrior, baseW, M.F_zero]
  law_nonneg := fun A h ε h0 h1 ω =>
    mul_nonneg (M.root.nonneg _) (Finset.prod_nonneg fun k _ => M.F_nonneg A h h0 h1 _ _ _)
  law_sum := fun A h ε =>
    M.sum_root_mul_pathLaw (M.F A h ε) fun r => pathLaw_sum_one_of_rowSum (M.F_rowSum A h ε r)

/-! ### Smoothness: every coordinate of the ε-law is a polynomial in `ε` -/

/-- Supporting lemma `differentiableAt_algW`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem differentiableAt_algW (A : Alg O Act Ξ N) (h : Node O N) (m : Node O N)
    (s : Fin (m.1.val + 1) → Ξ) (a : Act) : DifferentiableAt ℝ (fun ε => M.algW A h ε m s a) 0 := by
  unfold algW
  split_ifs
  · fun_prop
  · exact differentiableAt_const _

/-- Supporting lemma `differentiableAt_profW`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem differentiableAt_profW (A : Alg O Act Ξ N) (h : Node O N) (m : Node O N) (a' : Act) :
    DifferentiableAt ℝ (fun ε => M.profW A h ε m a') 0 := by
  unfold profW
  split_ifs
  · fun_prop
  · exact differentiableAt_const _

/-- Supporting lemma `differentiableAt_F` (each step factor is a polynomial in `ε`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem differentiableAt_F (A : Alg O Act Ξ N) (h : Node O N) (r : W × Ξ)
    (m : Node (Letter O Act Ξ) N) (ℓ : Letter O Act Ξ) :
    DifferentiableAt ℝ (fun ε => M.F A h ε r m ℓ) 0 := by
  have h1 := M.differentiableAt_algW A h (oNode m) (statePre r.2 m) ℓ.1
  have h2 : DifferentiableAt ℝ (fun ε => ∑ a', M.profW A h ε (M.pn (oNode m)) a' *
      (M.eA r.1 m.1 (obsPre m) (actPre m) ℓ.1 a').w ℓ.2.1) 0 :=
    DifferentiableAt.fun_sum fun a' _ => (M.differentiableAt_profW A h _ a').mul_const _
  exact (h1.mul h2).mul_const _

/-- **Post 6's Assumption 1 is a theorem of the model of record**: the ε-law is smooth (every
coordinate is a product of affine functions of `ε`), hence `A1` holds on the support.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080); mandate T7 (`A1`)
Kind: P
Fidelity: exact (on the support, see `A1`)
Hyps: (a) none -/
theorem smoothLaw : M.toPlaySpace.SmoothLaw := by
  intro A h ω
  show ∃ c, HasDerivAt (fun ε => M.lawW A h ε ω) c 0
  unfold lawW pathLaw
  exact ⟨_, (HasDerivAt.fun_finsetProd (u := (univ : Finset (Fin N)))
    (f := fun k ε => M.F A h ε ω.1 (prefixOf ω.2 k) (ω.2 k))
    (fun k _ => (M.differentiableAt_F A h ω.1 (prefixOf ω.2 k) (ω.2 k)).hasDerivAt)).const_mul
      (M.root.w ω.1)⟩

/-- Post 6's Assumption 1 on the support of the model of record.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080)
Kind: P
Fidelity: exact (on the support)
Hyps: (a) none -/
theorem A1 : M.toPlaySpace.A1 := M.toPlaySpace.A1_of_smoothLaw M.smoothLaw

end ProfileModel

end

end Cleanroom.Udt.UdtInfluence101
