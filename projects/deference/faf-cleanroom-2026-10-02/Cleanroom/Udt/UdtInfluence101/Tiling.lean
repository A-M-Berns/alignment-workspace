import Cleanroom.Udt.UdtInfluence101.Theorem1

/-!
# `Cleanroom.Udt.UdtInfluence101.Tiling`: UDT1.01 and Post 8's Theorem 2 (tiling) as weak dominance

Target T5 of [[udt-influence-101-mandate]].

* `IsUDT101 A h`: `A(h, S̄_h)` is a point mass on a maximizer of `f^0_{h,S̄_h}` at every positive-mass
  world reaching `h` (a predicate on algorithms, never a `Classical.choice` function).
* **Theorem 2**: under Theorem 1's hypotheses, `𝕀^𝔼_∅(A, h) ≤ 𝕀^𝔼_∅(UDT1.01, h)` — **weak dominance
  in time-0 influence, ties allowed**. "Tiling" here is not self-modification stability.
* **Non-uniqueness**: two maximizers at one positive-mass world give two distinct UDT1.01 algorithms
  (refuting the corpus's "unique algorithm" glosses, [[udt-influence-101-findings]]).
* **The tie class** (extension of record): `A` attains UDT1.01's influence at `h` iff, on every
  positive-mass world of the time-0 atom reaching `h`, `A(h, S̄_h)` puts its mass on maximizers of
  `f^0_{h,S̄_h}`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-- **UDT1.01 at `h`** (Post 8 §3.3: `UDT1.01(h, S̄_h) := argmax_a f^0_{h,S̄_h}(a)`), as a predicate on
algorithms: at every positive-mass world reaching `h`, `A(h, S̄_h)` is a point mass on a maximizer of
`a ↦ f^0_{h,S̄_h}(a)`. Ties are allowed (any maximizer), so the predicate is not a function. It
covers the *pure* selections only: the tie class of `tie_iff` is larger (a mixed algorithm supported
on maximizers ties in time-`0` influence without being `IsUDT101`).
Source: `references/udt101/08-actual-algorithm.md` §3.3 (udt-rep-083)
Kind: D
Fidelity: exact (restricted to positive-mass worlds reaching `h`, where the score is not junk)
Hyps: n/a -/
def IsUDT101 (A : Alg O Act Ξ N) (h : Node O N) : Prop :=
  ∀ ω, 0 < S.ℙ.w ω → ω ∈ S.reach h →
    ∃ a, S.play A h ω = FinDist.delta a ∧ IsArgmax (fun a' => S.fS h (FinDist.delta a') 0 ω) a

/-- Supporting lemma `exp_le_of_isArgmax` (`E_{a∼μ} f(a) ≤ f(a*)` for a maximizer `a*`; Post 8's
"basic math facts").
Source: `references/udt101/08-actual-algorithm.md` Theorem 2 proof
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exp_le_of_isArgmax (μ : FinDist Act) {f : Act → ℝ} {a : Act} (ha : IsArgmax f a) :
    ∑ a', μ.w a' * f a' ≤ f a := by
  calc ∑ a', μ.w a' * f a' ≤ ∑ a', μ.w a' * f a :=
        Finset.sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left (ha a') (μ.nonneg a')
    _ = f a := by rw [← Finset.sum_mul, μ.sum_one, one_mul]

/-- Supporting lemma `sum_delta_mul`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_delta_mul (a : Act) (f : Act → ℝ) : ∑ a', (FinDist.delta a).w a' * f a' = f a := by
  simp [FinDist.delta_w]

/-- Supporting lemma `cexp_mono_pos` (monotonicity of the finite conditional expectation, with the
inequality required only on positive-mass worlds).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_mono_pos {n : ℕ} {E : Finset Ω} {f g : Ω → ℝ} {ω : Ω}
    (hfg : ∀ ω' ∈ S.atom n ω ∩ E, 0 < S.ℙ.w ω' → f ω' ≤ g ω') :
    S.cexp S.ℙ.w n E f ω ≤ S.cexp S.ℙ.w n E g ω := by
  simp only [S.cexp_eq_div]
  refine div_le_div_of_nonneg_right ?_ (mass_nonneg S.ℙ.nonneg _)
  refine Finset.sum_le_sum fun ω' hω' => ?_
  rcases (S.ℙ.nonneg ω').lt_or_eq with h0 | h0
  · exact mul_le_mul_of_nonneg_left (hfg ω' hω' h0) h0.le
  · rw [← h0, zero_mul, zero_mul]

/-- **Post 8 Theorem 2 (tiling) as weak dominance**: under Theorem 1's hypotheses, if `A*` is a
UDT1.01 algorithm at `h`, then for every competitor `A` and every positive-mass world reaching `h`,
`𝕀^𝔼_∅(A, h) ≤ 𝕀^𝔼_∅(A*, h)` — the time-0 influence of `A*` is at least that of any algorithm, with
ties allowed. The post's clause "if Theorem 1, Lemma 2 … are true at time 0" is an LI-subjectivity
caveat with no classical content. "Tiling" is not self-modification stability: it is this inequality.
Source: `references/udt101/08-actual-algorithm.md` Theorem 2 (udt-rep-083); mandate T5(i)
Kind: P
Fidelity: exact (the influence is read at the time-0 atom of `ω`)
Hyps: as `theorem1` -/
theorem theorem2_tiling (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA3 : S.A3 h)
    (hA4 : S.A4 h) (hA5 : S.A5 h) (hRP : S.ReachPos h) {A' : Alg O Act Ξ N} (hU : S.IsUDT101 A' h)
    (A : Alg O Act Ξ N) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    S.IE 0 A h ω ≤ S.IE 0 A' h ω := by
  rw [S.theorem1_sum hS hall hA3 hA4 hA5 hRP A (Nat.zero_le _) hω hr,
    S.theorem1_sum hS hall hA3 hA4 hA5 hRP A' (Nat.zero_le _) hω hr]
  refine S.cexp_mono_pos fun ω' hω' hω'0 => ?_
  have hr' : ω' ∈ S.reach h := (Finset.mem_inter.1 hω').2
  obtain ⟨a, ha, hmax⟩ := hU ω' hω'0 hr'
  rw [ha, sum_delta_mul]
  exact exp_le_of_isArgmax _ hmax

/-! ### Measurability of the score at the horizon; existence of UDT1.01 algorithms -/

/-- Supporting lemma `ratio_measAt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ratio_measAt (h : Node O N) (n : ℕ) {ω ω' : Ω} (hω : S.AtomEq (n + 1) ω ω') :
    S.ratio h n ω' = S.ratio h n ω := by
  unfold ratio
  rw [← S.pr_measAt S.ℙ.w (n + 1) (S.reach h) ω ω' hω,
    ← S.pr_measAt S.ℙ.w n (S.reach h) ω ω' (S.atomEq_mono (Nat.le_succ n) hω)]

/-- **The score `f^n_{h,S̄_h}` is `𝔽_{|h|}`-measurable**: it depends on the world only through `h`'s
observations and `S̄_h` (so "`f^n_{h,S̄_h}`" is an honest name).
Source: `references/udt101/08-actual-algorithm.md` §3.1
Kind: L
Fidelity: exact
Hyps: none -/
theorem fS_measAt_horizon (h : Node O N) (μ : FinDist Act) {ω ω' : Ω} (hω : S.AtomEq h.1.val ω ω') :
    ∀ n, n ≤ h.1.val → S.fS h μ n ω' = S.fS h μ n ω := by
  suffices key : ∀ k n, n + k = h.1.val → S.fS h μ n ω' = S.fS h μ n ω by
    intro n hn; exact key (h.1.val - n) n (by omega)
  intro k
  induction k with
  | zero =>
    intro n hn
    have hnlt : ¬ n < h.1.val := by omega
    rw [S.fS_of_ge h μ hnlt, S.fS_of_ge h μ hnlt]
    exact S.fBase_measAt h μ n (S.atomEq_mono (by omega) hω)
  | succ k ih =>
    intro n hn
    have hlt : n < h.1.val := by omega
    rw [S.fS_of_lt h μ hlt, S.fS_of_lt h μ hlt, S.fBase_measAt h μ n (S.atomEq_mono hlt.le hω),
      S.fMid_measAt h μ hlt (S.atomEq_mono hlt.le hω), S.ratio_measAt h n (S.atomEq_mono (by omega) hω),
      ih (n + 1) (by omega)]

/-- Supporting lemma `atomEq_horizon_of_statesAlong_eq` (two positive worlds reaching `h` with the
same `S̄_h` share the time-`|h|` atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_horizon_of_statesAlong_eq {h : Node O N} {ω ω' : Ω} (hr : ω ∈ S.reach h)
    (hr' : ω' ∈ S.reach h) (hs : S.statesAlong ω h = S.statesAlong ω' h) : S.AtomEq h.1.val ω ω' := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [S.obs_eq_of_reach hr i hi, S.obs_eq_of_reach hr' i hi]
  · have := congrFun hs ⟨i.val, by omega⟩
    simpa [statesAlong] using this

/-- Supporting lemma `exists_argmax_score`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exists_argmax_score [Nonempty Act] (h : Node O N) (ω : Ω) :
    ∃ a, IsArgmax (fun a' => S.fS h (FinDist.delta a') 0 ω) a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image univ (fun a' => S.fS h (FinDist.delta a') 0 ω)
    Finset.univ_nonempty
  exact ⟨a, fun a' => ha a' (Finset.mem_univ _)⟩

open Classical in
/-- **A UDT1.01 algorithm** (one of possibly many): at `h`, on a state sequence realized by some
positive-mass world reaching `h`, play a maximizer of that world's `f^0_{h,S̄_h}`; elsewhere play an
arbitrary fixed action. A witness for `exists_isUDT101`; the predicate `IsUDT101`, not this
function, is the object of record.
Source: `references/udt101/08-actual-algorithm.md` §3.3
Kind: D
Fidelity: n/a (a witness)
Hyps: n/a -/
def udtAlg [Nonempty Act] (h : Node O N) : Alg O Act Ξ N := fun m s =>
  if hm : m = h then
    if hg : ∃ ω, 0 < S.ℙ.w ω ∧ ω ∈ S.reach h ∧
        S.statesAlong ω h = fun i => s ⟨i.val, by rw [hm]; exact i.isLt⟩ then
      FinDist.delta (Classical.choose (S.exists_argmax_score h (Classical.choose hg)))
    else FinDist.delta (Classical.arbitrary Act)
  else FinDist.delta (Classical.arbitrary Act)

/-- **UDT1.01 algorithms exist** (`N+`: the predicate is inhabited on every play space).
Source: `references/udt101/08-actual-algorithm.md` §3.3; mandate T5
Kind: N+
Fidelity: exact
Hyps: none -/
theorem isUDT101_udtAlg [Nonempty Act] (h : Node O N) : S.IsUDT101 (S.udtAlg h) h := by
  intro ω hω hr
  have hg : ∃ ω₁, 0 < S.ℙ.w ω₁ ∧ ω₁ ∈ S.reach h ∧
      S.statesAlong ω₁ h = fun i => S.statesAlong ω h ⟨i.val, i.isLt⟩ := ⟨ω, hω, hr, rfl⟩
  refine ⟨Classical.choose (S.exists_argmax_score h (Classical.choose hg)), ?_, ?_⟩
  · simp only [play, udtAlg, dite_true]
    exact dif_pos hg
  · obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hg
    have hat : S.AtomEq h.1.val (Classical.choose hg) ω :=
      S.atomEq_horizon_of_statesAlong_eq h2 hr h3
    have hmax := Classical.choose_spec (S.exists_argmax_score h (Classical.choose hg))
    intro a'
    show S.fS h (FinDist.delta a') 0 ω ≤
      S.fS h (FinDist.delta (Classical.choose (S.exists_argmax_score h (Classical.choose hg)))) 0 ω
    rw [S.fS_measAt_horizon h (FinDist.delta a') hat 0 (Nat.zero_le _),
      S.fS_measAt_horizon h (FinDist.delta _) hat 0 (Nat.zero_le _)]
    exact hmax a'

/-- Supporting lemma `exists_isUDT101`.
Source: none: infrastructure
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem exists_isUDT101 [Nonempty Act] (h : Node O N) : ∃ A, S.IsUDT101 A h :=
  ⟨S.udtAlg h, S.isUDT101_udtAlg h⟩

open Classical in
/-- `A` modified to play the pure action `a` at `h` on the state sequence `s₀` (and unchanged
elsewhere).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def modAt (A : Alg O Act Ξ N) (h : Node O N) (s₀ : Fin (h.1.val + 1) → Ξ) (a : Act) :
    Alg O Act Ξ N := fun m s =>
  if ∃ hm : m = h, (fun i => s ⟨i.val, by rw [hm]; exact i.isLt⟩) = s₀ then FinDist.delta a
  else A m s

/-- Supporting lemma `delta_injective`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem delta_injective {a b : Act} (h : (FinDist.delta a : FinDist Act) = FinDist.delta b) : a = b := by
  have := congrArg (fun μ : FinDist Act => μ.w a) h
  simp only [FinDist.delta_w, if_true] at this
  by_contra hne
  rw [if_neg hne] at this
  norm_num at this

/-- **UDT1.01 is not unique**: if at one positive-mass world reaching `h` the score `f^0_{h,S̄_h}` has
two distinct maximizers, there are two distinct UDT1.01 algorithms at `h`. This refutes the readings
"UDT1.01 is the unique algorithm where all instances agree to use it" and "under these axioms
`A = UDT1.01`" ([[diffractor-synthesis]] ll. 67, 194; ATTRIBUTION-UNVETTED — the note may have meant
"unique up to ties"); the surviving neighbour is `theorem2_tiling` + `tie_iff`.
Source: [[diffractor-synthesis]] ll. 67, 194 (udt-rep-083, 2-002(c)); mandate T5(ii), (iv)
Kind: P
Fidelity: exact (the conditional; the refutation of the uniqueness reading is carried by its
instances `Tie.two_udt101_hT` and `HomeTie.two_udt101_hH`)
Hyps: none beyond the tie at one world -/
theorem exists_two_isUDT101 [Nonempty Act] (h : Node O N) {ω₀ : Ω} (hω₀ : 0 < S.ℙ.w ω₀)
    (hr₀ : ω₀ ∈ S.reach h) {a₁ a₂ : Act} (hne : a₁ ≠ a₂)
    (h1 : IsArgmax (fun a => S.fS h (FinDist.delta a) 0 ω₀) a₁)
    (h2 : IsArgmax (fun a => S.fS h (FinDist.delta a) 0 ω₀) a₂) :
    ∃ A₁ A₂ : Alg O Act Ξ N, S.IsUDT101 A₁ h ∧ S.IsUDT101 A₂ h ∧ A₁ ≠ A₂ := by
  classical
  have key : ∀ a, IsArgmax (fun a' => S.fS h (FinDist.delta a') 0 ω₀) a →
      S.IsUDT101 (modAt (S.udtAlg h) h (S.statesAlong ω₀ h) a) h := by
    intro a ha ω hω hr
    by_cases hs : S.statesAlong ω h = S.statesAlong ω₀ h
    · refine ⟨a, ?_, ?_⟩
      · have hc : ∃ _hm : h = h, (fun i : Fin (h.1.val + 1) =>
            S.statesAlong ω h ⟨i.val, i.isLt⟩) = S.statesAlong ω₀ h := ⟨rfl, hs⟩
        show modAt (S.udtAlg h) h (S.statesAlong ω₀ h) a h (S.statesAlong ω h) = _
        unfold modAt
        rw [if_pos hc]
      · have hat := S.atomEq_horizon_of_statesAlong_eq hr₀ hr hs.symm
        intro a'
        show S.fS h (FinDist.delta a') 0 ω ≤ S.fS h (FinDist.delta a) 0 ω
        rw [S.fS_measAt_horizon h _ hat 0 (Nat.zero_le _), S.fS_measAt_horizon h _ hat 0 (Nat.zero_le _)]
        exact ha a'
    · obtain ⟨b, hb, hbmax⟩ := S.isUDT101_udtAlg h ω hω hr
      refine ⟨b, ?_, hbmax⟩
      rw [← hb]
      show modAt (S.udtAlg h) h (S.statesAlong ω₀ h) a h (S.statesAlong ω h) = _
      unfold modAt
      rw [if_neg]
      · rfl
      · rintro ⟨_, hs'⟩
        exact hs hs'
  refine ⟨_, _, key a₁ h1, key a₂ h2, fun heq => hne ?_⟩
  have hc : ∃ _hm : h = h, (fun i : Fin (h.1.val + 1) =>
      S.statesAlong ω₀ h ⟨i.val, i.isLt⟩) = S.statesAlong ω₀ h := ⟨rfl, rfl⟩
  have := congrFun (congrFun heq h) (S.statesAlong ω₀ h)
  unfold modAt at this
  rw [if_pos hc, if_pos hc] at this
  exact delta_injective this

/-! ### The tie class -/

/-- Supporting lemma `exp_eq_max_iff` (`E_{a∼μ} f(a) = max f` iff `μ` is supported on maximizers).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exp_eq_max_iff (μ : FinDist Act) {f : Act → ℝ} {a₀ : Act} (hmax : IsArgmax f a₀) :
    ∑ a, μ.w a * f a = f a₀ ↔ ∀ a, 0 < μ.w a → IsArgmax f a := by
  constructor
  · intro heq a ha
    by_contra hnot
    have hlt : f a < f a₀ := by
      by_contra hge
      exact hnot fun a' => le_trans (hmax a') (not_lt.1 hge)
    have : ∑ a', μ.w a' * f a' < ∑ a', μ.w a' * f a₀ :=
      Finset.sum_lt_sum (fun a' _ => mul_le_mul_of_nonneg_left (hmax a') (μ.nonneg a'))
        ⟨a, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt ha⟩
    rw [← Finset.sum_mul, μ.sum_one, one_mul] at this
    exact absurd heq this.ne
  · intro hsupp
    calc ∑ a, μ.w a * f a = ∑ a, μ.w a * f a₀ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rcases (μ.nonneg a).lt_or_eq with ha | ha
          · rw [le_antisymm (hmax a) (hsupp a ha a₀)]
          · rw [← ha, zero_mul, zero_mul]
      _ = f a₀ := by rw [← Finset.sum_mul, μ.sum_one, one_mul]

/-- **The tie class (extension of record)**: under Theorem 1's hypotheses, an algorithm `A` attains
UDT1.01's time-0 influence at `h` **iff** on every positive-mass world of the time-0 atom reaching
`h`, `A(h, S̄_h)` puts its mass on maximizers of `f^0_{h,S̄_h}`. (With a trivial time-0 state the atom
is everything: "mass on maximizers on every positive-probability world reaching `h`".)
Source: mandate T5(iii) (extension; plan: "the class of algorithms UDT1.01 only ties with")
Kind: P
Fidelity: exact
Hyps: as `theorem1` -/
theorem tie_iff (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA3 : S.A3 h) (hA4 : S.A4 h)
    (hA5 : S.A5 h) (hRP : S.ReachPos h) {A' : Alg O Act Ξ N} (hU : S.IsUDT101 A' h)
    (A : Alg O Act Ξ N) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    S.IE 0 A h ω = S.IE 0 A' h ω ↔
      ∀ ω' ∈ S.atom 0 ω ∩ S.reach h, 0 < S.ℙ.w ω' →
        ∀ a, 0 < (S.play A h ω').w a → IsArgmax (fun a' => S.fS h (FinDist.delta a') 0 ω') a := by
  rw [S.theorem1_sum hS hall hA3 hA4 hA5 hRP A (Nat.zero_le _) hω hr,
    S.theorem1_sum hS hall hA3 hA4 hA5 hRP A' (Nat.zero_le _) hω hr]
  have hpos : 0 < mass S.ℙ.w (S.atom 0 ω ∩ S.reach h) := S.mass_atom_inter_pos hω hr
  -- the pointwise gap is non-negative on positive worlds and the two expectations agree iff it vanishes
  rw [eq_comm, ← sub_eq_zero, ← S.cexp_sub, S.cexp_eq_div, div_eq_zero_iff, or_iff_left hpos.ne']
  have hnn : ∀ ω' ∈ S.atom 0 ω ∩ S.reach h, 0 ≤ S.ℙ.w ω' *
      (∑ a, (S.play A' h ω').w a * S.fS h (FinDist.delta a) 0 ω' -
        ∑ a, (S.play A h ω').w a * S.fS h (FinDist.delta a) 0 ω') := by
    intro ω' hω'
    rcases (S.ℙ.nonneg ω').lt_or_eq with h0 | h0
    · obtain ⟨b, hb, hbmax⟩ := hU ω' h0 (Finset.mem_inter.1 hω').2
      rw [hb, sum_delta_mul]
      exact mul_nonneg h0.le (sub_nonneg.2 (exp_le_of_isArgmax _ hbmax))
    · rw [← h0, zero_mul]
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro hz ω' hω' hω'0 a ha
    have := hz ω' hω'
    rw [mul_eq_zero, or_iff_right hω'0.ne', sub_eq_zero] at this
    obtain ⟨b, hb, hbmax⟩ := hU ω' hω'0 (Finset.mem_inter.1 hω').2
    rw [hb, sum_delta_mul] at this
    exact (exp_eq_max_iff _ hbmax).1 this.symm a ha
  · intro hsupp ω' hω'
    rcases (S.ℙ.nonneg ω').lt_or_eq with h0 | h0
    · obtain ⟨b, hb, hbmax⟩ := hU ω' h0 (Finset.mem_inter.1 hω').2
      rw [hb, sum_delta_mul, ((exp_eq_max_iff _ hbmax).2 (hsupp ω' hω' h0)), sub_self, mul_zero]
    · rw [← h0, zero_mul]

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
