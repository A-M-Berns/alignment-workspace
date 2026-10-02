import Cleanroom.Udt.UdtInfluence101.ProfileLemmas

/-!
# `Cleanroom.Udt.UdtInfluence101.ProfileA5`: Assumption 5 in the model of record

Target T7 of [[udt-influence-101-mandate]], the `A5` part. Abstractly, if the ε-law of an algorithm
on an atom is the `ν`-mixture of the ε-laws of the pure actions, its influences there are the
`ν`-average of the pure-action influences (`A5_at_of_law_mix`). In the model this mixture identity
holds pointwise when **each world has at most one ε-sensitive step** (`OneEps h`: no world both acts
at `h` and visits a node reading the profile at `h`, no world visits two such nodes, and `h` does not
read its own profile) and the algorithm's profile agrees with its action where a profile read
occurs (`lawW_mix`). Hence Post 8's Assumption 5 — for constant algorithms with no side condition
beyond `OneEps` (`A5_ofDist_model`), and for the time-`n` precommitments along `h` that Theorem 1's
proof needs, under the profile-coherence hypothesis `ProfCoherent` (`A5_model`).

**Finding F4**: without `OneEps`, Post 8's literal A5 still holds in the model (the derivative of a
product of affine factors is affine in `μ`), but the *extended* form fails in general: a
precommitment `Ā_{h,n}` reads unplannables, so its profile `prof A h` differs from its action
`Ā_{h,n}(h, S̄_h)` at time `n`, and a node that reads the profile at `h` sees the former while Post
8's `E_{a∼Ā}` step uses the latter. The general literal statement is recorded as OPEN
(`A5_ofDist_general`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ W : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] [Fintype W] [DecidableEq W] {N : ℕ}

namespace PlaySpace

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (S : PlaySpace O Act Ξ N Ω)

/-- Supporting lemma `dmass_of_law_mix` (the mass derivative of a mixture law is the mixture of the
mass derivatives).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dmass_of_law_mix (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) (ν : FinDist Act)
    {E : Finset Ω} (hmix : ∀ ε, ∀ ω' ∈ E, S.law A h ε ω' = ∑ a, ν.w a * S.law (ofAct a) h ε ω') :
    S.dmass A h E = ∑ a, ν.w a * S.dmass (ofAct a) h E := by
  unfold dmass
  have hpt : ∀ ω' ∈ E, deriv (fun ε => S.law A h ε ω') 0 =
      ∑ a, ν.w a * deriv (fun ε => S.law (ofAct a) h ε ω') 0 := by
    intro ω' hω'
    have hfun : (fun ε => S.law A h ε ω') = fun ε => ∑ a, ν.w a * S.law (ofAct a) h ε ω' :=
      funext fun ε => hmix ε ω' hω'
    rw [hfun]
    have hd : HasDerivAt (fun ε => ∑ a, ν.w a * S.law (ofAct a) h ε ω')
        (∑ a, ν.w a * deriv (fun ε => S.law (ofAct a) h ε ω') 0) 0 := by
      apply HasDerivAt.fun_sum
      intro a _
      obtain ⟨c, hc⟩ := hS (ofAct a) h ω'
      rw [hc.deriv]
      exact hc.const_mul _
    exact hd.deriv
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- Supporting lemma `dwsum_of_law_mix`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dwsum_of_law_mix (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) (ν : FinDist Act)
    {E : Finset Ω} (hmix : ∀ ε, ∀ ω' ∈ E, S.law A h ε ω' = ∑ a, ν.w a * S.law (ofAct a) h ε ω')
    (f : Ω → ℝ) : S.dwsum A h E f = ∑ a, ν.w a * S.dwsum (ofAct a) h E f := by
  unfold dwsum
  have hpt : ∀ ω' ∈ E, deriv (fun ε => S.law A h ε ω') 0 * f ω' =
      ∑ a, ν.w a * (deriv (fun ε => S.law (ofAct a) h ε ω') 0 * f ω') := by
    intro ω' hω'
    have hfun : (fun ε => S.law A h ε ω') = fun ε => ∑ a, ν.w a * S.law (ofAct a) h ε ω' :=
      funext fun ε => hmix ε ω' hω'
    rw [hfun]
    have hd : HasDerivAt (fun ε => ∑ a, ν.w a * S.law (ofAct a) h ε ω')
        (∑ a, ν.w a * deriv (fun ε => S.law (ofAct a) h ε ω') 0) 0 := by
      apply HasDerivAt.fun_sum
      intro a _
      obtain ⟨c, hc⟩ := hS (ofAct a) h ω'
      rw [hc.deriv]
      exact hc.const_mul _
    rw [hd.deriv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- **Affine influences from a mixture law**: if on the time-`n` atom of `ω` the ε-law of `A` is the
`ν`-mixture of the ε-laws of the pure actions, then at `(n, ω)` the influences of `A` are the
`ν`-averages of the pure-action influences (the `A5` identities at one epistemic state).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 ("a precommitment … is the same as a 50/50 mix of …")
Kind: P
Fidelity: exact
Hyps: (a) `SmoothLaw`; (a) positivity of the atom and of `atom ∩ {o}`; the mixture identity -/
theorem A5_at_of_law_mix (hS : S.SmoothLaw) {n : ℕ} {ω : Ω} (hatom : 0 < mass S.ℙ.w (S.atom n ω))
    (A : Alg O Act Ξ N) (h : Node O N) (ν : FinDist Act)
    (hmix : ∀ ε, ∀ ω' ∈ S.atom n ω, S.law A h ε ω' = ∑ a, ν.w a * S.law (ofAct a) h ε ω') (o : O)
    (hposo : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o)) :
    S.IP n A h o ω = ∑ a, ν.w a * S.IP n (ofAct a) h o ω ∧
      S.IEo n A h o ω = ∑ a, ν.w a * S.IEo n (ofAct a) h o ω := by
  have hmixF : ∀ ε, ∀ ω' ∈ S.nextObs n o ∩ S.atom n ω,
      S.law A h ε ω' = ∑ a, ν.w a * S.law (ofAct a) h ε ω' :=
    fun ε ω' hω' => hmix ε ω' (Finset.mem_inter.1 hω').2
  have hmixE : ∀ ε, ∀ ω' ∈ S.atom n ω ∩ S.nextObs n o,
      S.law A h ε ω' = ∑ a, ν.w a * S.law (ofAct a) h ε ω' :=
    fun ε ω' hω' => hmix ε ω' (Finset.mem_inter.1 hω').1
  constructor
  · simp only [IP, (S.hasDerivAt_pr hS _ h hatom (S.nextObs n o)).deriv]
    rw [S.dmass_of_law_mix hS A h ν hmixF, S.dmass_of_law_mix hS A h ν hmix]
    set m := mass S.ℙ.w (S.atom n ω)
    set mF := mass S.ℙ.w (S.nextObs n o ∩ S.atom n ω)
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_eq_mul_inv]
    ring
  · simp only [IEo, (S.hasDerivAt_cexp hS _ h hposo S.U).deriv]
    rw [S.dwsum_of_law_mix hS A h ν hmixE, S.dmass_of_law_mix hS A h ν hmixE]
    set m := mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o)
    set s₁ := ∑ ω' ∈ S.atom n ω ∩ S.nextObs n o, S.ℙ.w ω' * S.U ω'
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_eq_mul_inv]
    ring

end PlaySpace

namespace ProfileModel

variable (M : ProfileModel O Act Ξ W N)

/-- A letter-prefix is **ε-sensitive for `h`** when the environment at it mixes the action at `h` or
reads the profile at `h`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def EpsSens (h : Node O N) (m : Node (Letter O Act Ξ) N) : Prop :=
  oNode m = h ∨ M.pn (oNode m) = h

/-- **One ε-sensitive step per world**: no world has two ε-sensitive letters for `h`, and `h` does
not read its own profile. Under this condition every coordinate of the ε-law is affine in `ε`.
Source: none: infrastructure (sufficient condition for Assumption 5 in the model)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def OneEps (h : Node O N) : Prop :=
  (∀ (ω : PWorld O Act Ξ W N) (j j' : Fin N),
    M.EpsSens h (prefixOf ω.2 j) → M.EpsSens h (prefixOf ω.2 j') → j = j') ∧ M.pn h ≠ h

/-- Supporting lemma `F_eq_baseF_of_not_sens` (an insensitive step factor is the baseline one, for
every `ε` and every algorithm).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_eq_baseF_of_not_sens (A : Alg O Act Ξ N) {h : Node O N} (ε : ℝ) (r : W × Ξ)
    {m : Node (Letter O Act Ξ) N} (hm : ¬ M.EpsSens h m) (ℓ : Letter O Act Ξ) :
    M.F A h ε r m ℓ = M.baseF r m ℓ := by
  have h1 : oNode m ≠ h := fun h' => hm (Or.inl h')
  have h2 : M.pn (oNode m) ≠ h := fun h' => hm (Or.inr h')
  simp only [F, baseF, algW, profW, h1, h2, if_false]

/-- Supporting lemma `sum_mul_ofAct` (`Σ_a ν(a)·δ_a(b) = ν(b)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_mul_delta_w (ν : FinDist Act) (b : Act) :
    ∑ a, ν.w a * (FinDist.delta a : FinDist Act).w b = ν.w b := by
  simp [FinDist.delta_w]

/-- **At a step that mixes the action at `h` (and reads no profile at `h`), the step factor is the
`ν`-mixture of the pure-action step factors**, when the algorithm's action there is `ν`.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_mix_act (A : Alg O Act Ξ N) {h : Node O N} (ε : ℝ) (r : W × Ξ)
    {m : Node (Letter O Act Ξ) N} (hm : oNode m = h) (hnp : M.pn (oNode m) ≠ h) (ν : FinDist Act)
    (hact : A (oNode m) (statePre r.2 m) = ν) (ℓ : Letter O Act Ξ) :
    M.F A h ε r m ℓ = ∑ a, ν.w a * M.F (ofAct a) h ε r m ℓ := by
  have hnp' : M.pn h ≠ h := by rw [hm] at hnp; exact hnp
  simp only [F, algW, profW, hm, hnp', if_true, if_false, hact, ofAct, ofDist]
  have e1 : ∑ b, ν.w b * ((1 - ε) * (M.B (oNode m) (statePre r.2 m)).w ℓ.1) =
      (1 - ε) * (M.B (oNode m) (statePre r.2 m)).w ℓ.1 := by
    rw [← Finset.sum_mul, ν.sum_one, one_mul]
  have e2 : ∑ b, ν.w b * (ε * (FinDist.delta b : FinDist Act).w ℓ.1) = ε * ν.w ℓ.1 := by
    simp only [mul_left_comm _ ε, ← Finset.mul_sum]
    rw [sum_mul_delta_w]
  have key : (∑ b, ν.w b * ((1 - ε) * (M.B (oNode m) (statePre r.2 m)).w ℓ.1 +
      ε * (FinDist.delta b : FinDist Act).w ℓ.1)) =
      (1 - ε) * (M.B (oNode m) (statePre r.2 m)).w ℓ.1 + ε * ν.w ℓ.1 := by
    rw [Finset.sum_congr rfl fun b _ => mul_add _ _ _, Finset.sum_add_distrib, e1, e2]
  rw [← key, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Supporting lemma `prof_ofAct` (the profile of a pure action is that action, on a positive
`reach h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_ofAct {h : Node O N} (hreach : 0 < mass M.baseW (pReach h)) (a : Act) :
    M.prof (ofAct a) h = FinDist.delta a := by
  apply FinDist.ext
  intro b
  rw [M.prof_w_of_pos _ hreach]
  exact condExpJunk_const_on (fun _ _ => rfl) hreach

/-- **At a step that reads the profile at `h` (and is not `h`), the step factor is the `ν`-mixture of
the pure-action step factors**, when the algorithm's profile at `h` is `ν`.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_mix_prof (A : Alg O Act Ξ N) {h : Node O N} (hreach : 0 < mass M.baseW (pReach h)) (ε : ℝ)
    (r : W × Ξ) {m : Node (Letter O Act Ξ) N} (hm : oNode m ≠ h) (hp : M.pn (oNode m) = h)
    (ν : FinDist Act) (hprof : M.prof A h = ν) (ℓ : Letter O Act Ξ) :
    M.F A h ε r m ℓ = ∑ a, ν.w a * M.F (ofAct a) h ε r m ℓ := by
  simp only [F, algW, profW, hm, hp, if_true, if_false, hprof, M.prof_ofAct hreach]
  set e : Act → ℝ := fun a' => (M.eA r.1 m.1 (obsPre m) (actPre m) ℓ.1 a').w ℓ.2.1 with he
  have key : (∑ b, ν.w b * ∑ a', ((1 - ε) * (M.π₀ h).w a' + ε * (FinDist.delta b : FinDist Act).w a') * e a') =
      ∑ a', ((1 - ε) * (M.π₀ h).w a' + ε * ν.w a') * e a' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have e1 : ∑ b, ν.w b * ((1 - ε) * (M.π₀ h).w a' * e a') = (1 - ε) * (M.π₀ h).w a' * e a' := by
      rw [← Finset.sum_mul, ν.sum_one, one_mul]
    have e2 : ∑ b, ν.w b * (ε * (FinDist.delta b : FinDist Act).w a' * e a') = ε * ν.w a' * e a' := by
      have : ∀ b, ν.w b * (ε * (FinDist.delta b : FinDist Act).w a' * e a') =
          (ε * e a') * (ν.w b * (FinDist.delta b : FinDist Act).w a') := fun b => by ring
      simp only [this, ← Finset.mul_sum]
      rw [sum_mul_delta_w]
      ring
    rw [Finset.sum_congr rfl fun b _ => by rw [add_mul, mul_add], Finset.sum_add_distrib, e1, e2]
    ring
  rw [← key, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The ε-law of a world is the `ν`-mixture of the pure-action ε-laws** when the world has at most
one ε-sensitive step and the algorithm is `ν`-coherent there (its action at `h` is `ν` if the
sensitive step is at `h`; its profile at `h` is `ν` if the sensitive step reads `h`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (the "50/50 mix" motivation, made exact)
Kind: P
Fidelity: exact
Hyps: none beyond `OneEps h` and the coherence of the algorithm at the world -/
theorem lawW_mix (A : Alg O Act Ξ N) {h : Node O N} (hone : M.OneEps h)
    (hreach : 0 < mass M.baseW (pReach h)) (ε : ℝ) (ω : PWorld O Act Ξ W N) (ν : FinDist Act)
    (hact : ∀ j : Fin N, oNode (prefixOf ω.2 j) = h →
      A (oNode (prefixOf ω.2 j)) (statePre ω.1.2 (prefixOf ω.2 j)) = ν)
    (hprof : ∀ j : Fin N, M.pn (oNode (prefixOf ω.2 j)) = h → M.prof A h = ν) :
    M.lawW A h ε ω = ∑ a, ν.w a * M.lawW (ofAct a) h ε ω := by
  have hmixF : ∀ j : Fin N, M.EpsSens h (prefixOf ω.2 j) →
      M.F A h ε ω.1 (prefixOf ω.2 j) (ω.2 j) = ∑ a, ν.w a * M.F (ofAct a) h ε ω.1 (prefixOf ω.2 j) (ω.2 j) := by
    intro j hj
    by_cases hm : oNode (prefixOf ω.2 j) = h
    · exact M.F_mix_act A ε ω.1 hm (by rw [hm]; exact hone.2) ν (hact j hm) _
    · have hp : M.pn (oNode (prefixOf ω.2 j)) = h := hj.resolve_left hm
      exact M.F_mix_prof A hreach ε ω.1 hm hp ν (hprof j hp) _
  unfold lawW pathLaw
  by_cases hex : ∃ j : Fin N, M.EpsSens h (prefixOf ω.2 j)
  · obtain ⟨j₀, hj₀⟩ := hex
    have hins : ∀ j ∈ (univ : Finset (Fin N)).erase j₀, ¬ M.EpsSens h (prefixOf ω.2 j) := by
      intro j hj hs
      exact (Finset.mem_erase.1 hj).1 (hone.1 ω j j₀ hs hj₀)
    have hprodA : ∀ A' : Alg O Act Ξ N, ∏ k, M.F A' h ε ω.1 (prefixOf ω.2 k) (ω.2 k) =
        M.F A' h ε ω.1 (prefixOf ω.2 j₀) (ω.2 j₀) *
          ∏ k ∈ univ.erase j₀, M.baseF ω.1 (prefixOf ω.2 k) (ω.2 k) := by
      intro A'
      rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ j₀)]
      congr 1
      exact Finset.prod_congr rfl fun k hk => M.F_eq_baseF_of_not_sens A' ε ω.1 (hins k hk) _
    simp only [hprodA]
    rw [hmixF j₀ hj₀, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp only [not_exists] at hex
    have hbase : ∀ A' : Alg O Act Ξ N, ∏ k, M.F A' h ε ω.1 (prefixOf ω.2 k) (ω.2 k) =
        ∏ k, M.baseF ω.1 (prefixOf ω.2 k) (ω.2 k) := fun A' =>
      Finset.prod_congr rfl fun k _ => M.F_eq_baseF_of_not_sens A' ε ω.1 (hex k) _
    simp only [hbase]
    rw [← Finset.sum_mul, ν.sum_one, one_mul]

/-- Supporting lemma `statePre_prefixOf` (the states along a letter-prefix of a world are the
world's states along the corresponding plannable history).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem statePre_prefixOf (ω : PWorld O Act Ξ W N) (j : Fin N) :
    statePre ω.1.2 (prefixOf ω.2 j) = pStatesAlong ω (oNode (prefixOf ω.2 j)) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · show statePre ω.1.2 (prefixOf ω.2 j) 0 = pStatesAlong ω (oNode (prefixOf ω.2 j)) 0
    rfl
  · show statePre ω.1.2 (prefixOf ω.2 j) k.succ = pStatesAlong ω (oNode (prefixOf ω.2 j)) k.succ
    rfl

/-- **Post 8's Assumption 5 for constant algorithms holds in the model of record** (under `OneEps h`
and full support of the next observation): the ε-law of a constant algorithm is the mixture of the
pure-action ε-laws, hence so are its influences.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081); mandate T7 (`A5`)
Kind: P
Fidelity: exact (Post 8's literal statement, along `h`)
Hyps: (a) `OneEps h`, `0 < ℙ(reach h)`, `AllPosObs` (regularity, checked on the instance) -/
theorem A5_ofDist_model {h : Node O N} (hone : M.OneEps h) (hreach : 0 < mass M.baseW (pReach h))
    (hall : M.toPlaySpace.AllPosObs) {n : ℕ} (hn : n ≤ h.1.val) (μ : FinDist Act)
    {ω : PWorld O Act Ξ W N} (hω : 0 < M.baseW ω) (o : O) :
    M.toPlaySpace.IP n (ofDist μ) h o ω = ∑ a, μ.w a * M.toPlaySpace.IP n (ofAct a) h o ω ∧
      M.toPlaySpace.IEo n (ofDist μ) h o ω = ∑ a, μ.w a * M.toPlaySpace.IEo n (ofAct a) h o ω := by
  have hnN : n < N := lt_of_le_of_lt hn h.1.isLt
  refine M.toPlaySpace.A5_at_of_law_mix M.smoothLaw (M.toPlaySpace.mass_atom_pos hω) (ofDist μ) h μ
    (fun ε ω' _ => ?_) o (hall n hnN ω hω o)
  exact M.lawW_mix (ofDist μ) hone hreach ε ω' μ (fun _ _ => rfl) (fun _ _ => by
    apply FinDist.ext; intro b
    rw [M.prof_w_of_pos _ hreach]
    exact condExpJunk_const_on (fun _ _ => rfl) hreach)

/-- **Profile coherence of time-`n` precommitments**: at every epistemic state along `h`, an
algorithm whose action at `h` is constant on the atom has, if any world of the atom visits a node
reading the profile at `h`, that constant as its profile. (In the instance of record this holds
because the only such reads happen at time `0`, where the atom is everything.)
Source: none: infrastructure (hypothesis of `A5_model`; finding F4 explains why it is needed)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ProfCoherent (h : Node O N) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ h.1.val) (A : Alg O Act Ξ N) (ω : PWorld O Act Ξ W N), 0 < M.baseW ω →
    M.toPlaySpace.Along h n hn ω → M.toPlaySpace.ConstOnAtom n A h ω →
    ∀ ω' ∈ M.toPlaySpace.atom n ω, ∀ j : Fin N, M.pn (oNode (prefixOf ω'.2 j)) = h →
      M.prof A h = M.toPlaySpace.play A h ω

/-- **Post 8's Assumption 5, in the time-`n`-precommitment form Theorem 1 uses, holds in the model
of record** under `OneEps h` and profile coherence.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 and the proof of Theorem 1; mandate T7 (`A5`)
Kind: P
Fidelity: exact (the `A5` predicate of `Defs`)
Hyps: (a) `OneEps h`, `0 < ℙ(reach h)`, `AllPosObs`, `ProfCoherent h` (regularity, checked on the instance) -/
theorem A5_model {h : Node O N} (hone : M.OneEps h) (hreach : 0 < mass M.baseW (pReach h))
    (hall : M.toPlaySpace.AllPosObs) (hcoh : M.ProfCoherent h) : M.toPlaySpace.A5 h := by
  intro n hn A ω hω hal hconst o
  have hnN : n < N := lt_of_le_of_lt hn h.1.isLt
  refine M.toPlaySpace.A5_at_of_law_mix M.smoothLaw (M.toPlaySpace.mass_atom_pos hω) A h
    (M.toPlaySpace.play A h ω) (fun ε ω' hω' => ?_) o (hall n hnN ω hω o)
  refine M.lawW_mix A hone hreach ε ω' _ (fun j hj => ?_) (fun j hj => hcoh n hn A ω hω hal hconst ω' hω' j hj)
  rw [statePre_prefixOf, hj]
  exact hconst ω' hω'

/-- **OPEN — the probability half (`IP` clause) of Post 8's literal Assumption 5 in the model without
`OneEps`**: the derivative at `0` of a product of factors affine in `ε` with slopes affine in `μ` is
affine in `μ`, so the identity should hold for every constant algorithm in every profile-predictor
model; not formalized here (the `OneEps` route was taken for the instance of record). Post 8's `IEo`
display is not stated.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5; mandate T7
Kind: OPEN
Fidelity: weaker: the `IP` clause only
Hyps: (a) `0 < ℙ(reach h)`, `AllPosObs` -/
theorem A5_ofDist_general {h : Node O N} (hreach : 0 < mass M.baseW (pReach h))
    (hall : M.toPlaySpace.AllPosObs) {n : ℕ} (hn : n ≤ h.1.val) (μ : FinDist Act)
    {ω : PWorld O Act Ξ W N} (hω : 0 < M.baseW ω) (o : O) :
    M.toPlaySpace.IP n (ofDist μ) h o ω = ∑ a, μ.w a * M.toPlaySpace.IP n (ofAct a) h o ω := by
  sorry

end ProfileModel

end

end Cleanroom.Udt.UdtInfluence101
