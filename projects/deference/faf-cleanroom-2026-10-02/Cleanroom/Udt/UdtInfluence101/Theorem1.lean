import Cleanroom.Udt.UdtInfluence101.Calculus

/-!
# `Cleanroom.Udt.UdtInfluence101.Theorem1`: Post 8's Theorem 1 — influence is the expected score

Target T4 of [[udt-influence-101-mandate]]: on a smooth play space with full support of the next
observation, Post 6's Assumption 3, Post 7's Assumption 4 and Post 8's Assumption 5 (as named
predicates, (b)), at every positive-mass world reaching `h` and every `n ≤ |h|`,

`𝕀^𝔼_{h₁:ₙ}(A, h) = 𝔼_{h₁:ₙ}[ f^n_{h,S̄_h}(A(h, S̄_h)) | h ]`.

The proof is Post 8's downward induction. Everything the post calls "expectation shuffling" is a
lemma of the finite play space here: the expectation of a function of the average
(`sum_avg_mul`), measurability of the time-`n` quantities, the regrouping identity
(`PlaySpace.sum_cexp_regroup`) and fast feedback. Two positivity facts the post leaves implicit are
hypotheses: `AllPosObs` (Lemma 1 divides by `ℙ_{h₁:ₙ}(o)`) and `ReachPos h` (the proof divides by
`ℙ_{h₁:ₙ₊₁}(h)` on every time-`(n+1)` atom below `h_{n+1}`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-! ### Expectation of a function of the average; measurability of the score's pieces -/

/-- Supporting lemma `play_avg_w` (the weights of `Ā_{h,n}(h, S̄_h)` at a positive-mass world
reaching `h` are the conditional expectations `ℙ_{h₁:ₙ}(A(h,S̄_h) = a | h)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_avg_w (A : Alg O Act Ξ N) {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω}
    (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) (a : Act) :
    (S.play (S.avg A h n) h ω).w a =
      condExpJunk S.ℙ.w (fun ω' => (S.play A h ω').w a) (S.atom n ω ∩ S.reach h) 0 := by
  rw [S.play_avg, S.avgDist_w_of_pos (S.avgEvent_pos hn hω hr), S.avgEvent_eq hn hr]

/-- **Expectation of a function of the average** (Post 8: `E_{a∼Ā_{h,n}}[f(a)] = 𝔼_{h₁:ₙ}[f(A(h,S̄_h)) | h]`,
which the post justifies by a Dutch book; here it is the tower property plus linearity).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof ("it's possible to show a trader can extract free money if …")
Kind: L
Fidelity: exact (finite form)
Hyps: none -/
theorem sum_avg_mul (A : Alg O Act Ξ N) {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω}
    (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) (g : Act → ℝ) :
    ∑ a, (S.play (S.avg A h n) h ω).w a * g a =
      S.cexp S.ℙ.w n (S.reach h) (fun ω' => ∑ a, (S.play A h ω').w a * g a) ω := by
  have hpos : 0 < mass S.ℙ.w (S.atom n ω ∩ S.reach h) := S.mass_atom_inter_pos hω hr
  simp only [S.play_avg_w A hn hω hr]
  rw [← S.cexp_sum hpos]
  refine Finset.sum_congr rfl fun a _ => ?_
  change S.cexp S.ℙ.w n (S.reach h) (fun ω' => (S.play A h ω').w a) ω * g a = _
  rw [mul_comm, ← S.cexp_const_mul]
  congr 1
  funext ω'
  ring

/-- Supporting lemma `fBase_measAt` (the causal term is `𝔽_n`-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fBase_measAt (h : Node O N) (μ : FinDist Act) (n : ℕ) {ω ω' : Ω} (hω : S.AtomEq n ω ω') :
    S.fBase h μ n ω' = S.fBase h μ n ω := by
  unfold fBase
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← S.pr_measAt S.ℙ.w n (S.nextObs n o) ω ω' hω, ← S.IEo_measAt n (ofDist μ) h o ω ω' hω,
    ← S.IP_measAt n (ofDist μ) h o ω ω' hω, ← S.cexp_measAt S.ℙ.w n (S.nextObs n o) S.U ω ω' hω]

/-- Supporting lemma `fMid_measAt` (the deferral-correction term is `𝔽_n`-measurable).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fMid_measAt (h : Node O N) (μ : FinDist Act) {n : ℕ} (hn : n < h.1.val) {ω ω' : Ω}
    (hω : S.AtomEq n ω ω') : S.fMid h μ n hn ω' = S.fMid h μ n hn ω := by
  unfold fMid
  rw [← S.pr_measAt S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω ω' hω,
    ← S.cexp_measAt S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) _ ω ω' hω]

/-- Supporting lemma `fBase_eq_sum_fBase_delta` (Lemma 2's base at the world `ω'` of the inner
expectation, with the pure-action scores read at the outer world `ω` of the same atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fBase_play_eq {h : Node O N} (hA5 : S.A5 h) (A : Alg O Act Ξ N) {n : ℕ} (hn : n ≤ h.1.val)
    {ω ω' : Ω} (hω : S.AtomEq n ω ω') (hω' : 0 < S.ℙ.w ω') (hal' : S.Along h n hn ω') :
    S.fBase h (S.play A h ω') n ω' = ∑ a, (S.play A h ω').w a * S.fBase h (FinDist.delta a) n ω := by
  rw [S.fBase_affine hA5 hn _ hω' hal']
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [S.fBase_measAt h _ n hω]

/-! ### Step A: Lemma 1, Assumption 3 and Assumption 4 at time `n < |h|` -/

/-- **The partial end result of Post 6 with Assumption 4 applied** (Post 7 §2.9's display, corrected):
for `n < |h|`, at a positive-mass world reaching `h`,
`𝕀^𝔼_{h₁:ₙ}(A,h) = Σ_o (ℙ(o)𝕀^𝔼(Ā,h,o) + 𝕀^ℙ(Ā,h,o)𝔼[U|o]) − ℙ(h_{n+1})𝔼[𝕀^𝔼_{n+1}(Ā,h) | h_{n+1}] + ℙ(h_{n+1})𝔼[𝕀^𝔼_{n+1}(A,h) | h_{n+1}]`.
Source: `references/udt101/06-basics-of-algorithm.md` "Partial End Result"; `07-conservation-of-expected-gain.md` §2.9; `08-actual-algorithm.md` Theorem 1 proof (first two displays)
Kind: C
Fidelity: exact
Hyps: (a) `SmoothLaw`, `PosObs`; (b) `A3` (Post 6), (b) `A4` (Post 7) -/
theorem IE_step_split (hS : S.SmoothLaw) {h : Node O N} (hA3 : S.A3 h) (hA4 : S.A4 h)
    (A : Alg O Act Ξ N) {n : ℕ} (hn : n < h.1.val) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h)
    (hpos : S.PosObs n ω) :
    S.IE n A h ω =
      (∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n (S.avg A h n) h o ω +
          S.IP n (S.avg A h n) h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω))
        - S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
            S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) (S.avg A h n) h ω') ω
        + S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
            S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) A h ω') ω := by
  have hnN : n < N := lt_trans hn h.1.isLt
  rw [S.lemma1_split hS hnN hpos]
  obtain ⟨h3P, h3E⟩ := hA3 n hn.le A ω hω hr
  have h4 := hA4 n hn A ω hω hr
  rw [S.cexp_sub] at h4
  set o₀ := h.2 ⟨n, hn⟩ with ho₀
  -- separate the escape-clause observation
  have hsplit : ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n A h o ω +
      S.IP n A h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω) =
      (∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n (S.avg A h n) h o ω +
          S.IP n (S.avg A h n) h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω)) +
        S.pr S.ℙ.w n (S.nextObs n o₀) ω * (S.IEo n A h o₀ ω - S.IEo n (S.avg A h n) h o₀ ω) := by
    rw [← Finset.sum_eq_single (s := univ) o₀
      (f := fun o => S.pr S.ℙ.w n (S.nextObs n o) ω * (S.IEo n A h o ω - S.IEo n (S.avg A h n) h o ω))
      (fun o _ ho => by rw [h3E o (fun _ => ho), sub_self, mul_zero]) (fun habs => absurd (Finset.mem_univ _) habs)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [h3P o]
    ring
  rw [hsplit, h4]
  ring

/-! ### Step C: Post 8 Lemma 1 for the averaged algorithm at time `n + 1` -/

/-- Supporting lemma `play_avg_eq_of_mem_atom` (`Ā_{h,n}(h, ·)` is constant on the time-`n` atom
of a positive-mass world reaching `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_avg_eq_of_mem_atom (A : Alg O Act Ξ N) {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω}
    (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) {ω' : Ω} (hω' : S.AtomEq n ω ω') :
    S.play (S.avg A h n) h ω' = S.play (S.avg A h n) h ω :=
  S.play_avg_eq_of_atomEq A h (S.avgEvent_pos hn hω hr) hω'

/-- **Post 8 Lemma 1 for `Ā_{h,n}` at time `n + 1`** ("Using Lemma 1, on affineness of influence"):
at a positive-mass world `ω'` of the time-`n` atom of `ω`, `𝕀^𝔼_{h₁:ₙ₊₁}(Ā_{h,n}, h) = E_{a∼Ā_{h,n}}[𝕀^𝔼_{h₁:ₙ₊₁}(a, h)]`,
with the weights `Ā_{h,n}(h, S̄_h)(ω)` fixed at time `n`.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof (the `ℙ(h_{n+1})𝔼[𝕀^𝔼_{n+1}(Ā_{h,n},h)|h_{n+1}]` term)
Kind: C
Fidelity: exact
Hyps: (a) `SmoothLaw`, `AllPosObs`; (b) `A5` (applied to the time-`n` precommitment `Ā_{h,n}`) -/
theorem IE_avg_succ_affine (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA5 : S.A5 h)
    (A : Alg O Act Ξ N) {n : ℕ} (hn : n < h.1.val) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h)
    {ω' : Ω} (hω' : S.AtomEq n ω ω') (hω'n : ω' ∈ S.nextObs n (h.2 ⟨n, hn⟩)) (hω'0 : 0 < S.ℙ.w ω') :
    S.IE (n + 1) (S.avg A h n) h ω' =
      ∑ a, (S.play (S.avg A h n) h ω).w a * S.IE (n + 1) (ofAct a) h ω' := by
  have hnN : n + 1 < N := lt_of_le_of_lt hn h.1.isLt
  have hpos' : S.PosObs (n + 1) ω' := hall (n + 1) hnN ω' hω'0
  have hconst : S.ConstOnAtom (n + 1) (S.avg A h n) h ω' := fun ω'' hω'' =>
    (S.play_avg_eq_of_mem_atom A hn.le hω hr
      (S.atomEq_trans hω' (S.atomEq_mono (Nat.le_succ n) (S.mem_atom.1 hω'')))).trans
      (S.play_avg_eq_of_mem_atom A hn.le hω hr hω').symm
  rw [S.lemma1_split hS hnN hpos']
  have h5 := hA5 (n + 1) hn (S.avg A h n) ω' hω'0 (S.along_succ hn (S.along_of_reach _ hr) hω' hω'n) hconst
  simp only [(h5 _).1, (h5 _).2, S.play_avg_eq_of_mem_atom A hn.le hω hr hω']
  rw [sum_affine_combo]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [S.lemma1_split hS hnN hpos' (ofAct a) h]

/-! ### Step B and Step C: the two `Ā_{h,n}` terms as conditional expectations over `reach h` -/

/-- **Step B of Post 8's proof**: the causal term for `Ā_{h,n}` equals
`𝔼_{h₁:ₙ}[ causal term for A(h, S̄_h) | h ]` (affineness for the precommitment `Ā_{h,n}`, then the
expectation of a function of the average, then Lemma 2's base at the inner world).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof (first term)
Kind: C
Fidelity: exact
Hyps: (b) `A5` -/
theorem term1_eq {h : Node O N} (hA5 : S.A5 h) (A : Alg O Act Ξ N) {n : ℕ} (hn : n ≤ h.1.val)
    {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n (S.avg A h n) h o ω +
        S.IP n (S.avg A h n) h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω) =
      S.cexp S.ℙ.w n (S.reach h) (fun ω' => S.fBase h (S.play A h ω') n ω') ω := by
  have hconst : S.ConstOnAtom n (S.avg A h n) h ω :=
    S.avg_constOnAtom A (S.avgEvent_pos hn hω hr)
  have h5 := hA5 n hn (S.avg A h n) ω hω (S.along_of_reach _ hr) hconst
  simp only [(h5 _).1, (h5 _).2]
  rw [sum_affine_combo]
  change ∑ a, (S.play (S.avg A h n) h ω).w a * S.fBase h (FinDist.delta a) n ω = _
  rw [S.sum_avg_mul A hn hω hr]
  exact S.cexp_congr_on_pos fun ω' hω' hω'0 =>
    (S.fBase_play_eq hA5 A hn (S.mem_atom.1 (Finset.mem_inter.1 hω').1) hω'0
      (S.along_of_reach _ (Finset.mem_inter.1 hω').2)).symm

/-- **Step C of Post 8's proof**: the deferral-correction term for `Ā_{h,n}` equals
`𝔼_{h₁:ₙ}[ deferral-correction term for A(h, S̄_h) | h ]`.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof (second term)
Kind: C
Fidelity: exact
Hyps: (a) `SmoothLaw`, `AllPosObs`; (b) `A5` -/
theorem term2_eq (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA5 : S.A5 h)
    (A : Alg O Act Ξ N) {n : ℕ} (hn : n < h.1.val) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
        S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) (S.avg A h n) h ω') ω =
      S.cexp S.ℙ.w n (S.reach h) (fun ω' => S.fMid h (S.play A h ω') n hn ω') ω := by
  have hposE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) :=
    hall n (lt_trans hn h.1.isLt) ω hω _
  rw [S.cexp_congr_on_pos (g := fun ω' => ∑ a, (S.play (S.avg A h n) h ω).w a *
      S.IE (n + 1) (ofAct a) h ω') fun ω' hω' hω'0 =>
    S.IE_avg_succ_affine hS hall hA5 A hn hω hr (S.mem_atom.1 (Finset.mem_inter.1 hω').1)
      (Finset.mem_inter.1 hω').2 hω'0]
  rw [← S.cexp_sum hposE]
  simp only [S.cexp_const_mul]
  rw [Finset.mul_sum]
  have hre : ∑ a, S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω * ((S.play (S.avg A h n) h ω).w a *
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) (ofAct a) h ω') ω) =
      ∑ a, (S.play (S.avg A h n) h ω).w a * (S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) (ofAct a) h ω') ω) :=
    Finset.sum_congr rfl fun a _ => by ring
  rw [hre, S.sum_avg_mul A hn.le hω hr]
  refine S.cexp_congr_on_pos fun ω' hω' hω'0 => ?_
  have hat : S.AtomEq n ω ω' := S.mem_atom.1 (Finset.mem_inter.1 hω').1
  rw [S.fMid_affine hS hall hA5 hn _ hω'0 (S.along_of_reach _ (Finset.mem_inter.1 hω').2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [S.fMid_measAt h _ hn hat]
  rfl

/-! ### Step D: the induction term, via the regrouping identity -/

/-- Supporting lemma `exists_pos_of_mass_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.exists_pos_of_mass_pos {X : Type} {w : X → ℝ}
    {E : Finset X} (h : 0 < mass w E) : ∃ x ∈ E, 0 < w x := by
  by_contra hcon
  exact absurd h (not_lt.2 (Finset.sum_nonpos fun x hx =>
    not_lt.1 fun hpos => hcon ⟨x, hx, hpos⟩))

/-- **Step D of Post 8's proof** ("unpack the conditional expectation … collapse the two layers …
multiply by 1"): for `n < |h|`, at a positive-mass world reaching `h`, and any `F`,
`ℙ_{h₁:ₙ}(h_{n+1}) · 𝔼_{h₁:ₙ}[ 𝔼_{h₁:ₙ₊₁}[F | h] | h_{n+1} ] = 𝔼_{h₁:ₙ}[ (ℙ_{h₁:ₙ}(h)/ℙ_{h₁:ₙ₊₁}(h)) · F | h ]`.
Pure finite measure algebra: fast feedback is the inclusion `reach h ⊆ {h_{n+1}}`, the collapse is
the regrouping identity; no positivity beyond the world `ω` itself is needed, since null atoms
contribute nothing on either side.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof (third term)
Kind: P
Fidelity: exact (finite form)
Hyps: none -/
theorem pr_mul_cexp_cexp_eq {h : Node O N} {n : ℕ} (hn : n < h.1.val) {ω : Ω} (hω : 0 < S.ℙ.w ω)
    (hr : ω ∈ S.reach h) (F : Ω → ℝ) :
    S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
        S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩))
          (fun ω' => S.cexp S.ℙ.w (n + 1) (S.reach h) F ω') ω =
      S.cexp S.ℙ.w n (S.reach h) (fun ω' => S.ratio h n ω' * F ω') ω := by
  set E := S.nextObs n (h.2 ⟨n, hn⟩) with hEdef
  have hrE : S.reach h ⊆ E := S.reach_subset_nextObs hn
  have hωE : ω ∈ E := hrE hr
  have hposAE : 0 < mass S.ℙ.w (S.atom n ω ∩ E) := S.mass_atom_inter_pos hω hωE
  have hposAt : 0 < mass S.ℙ.w (S.atom n ω) := S.mass_atom_pos hω
  have hposAR : 0 < mass S.ℙ.w (S.atom n ω ∩ S.reach h) := S.mass_atom_inter_pos hω hr
  have hclosed : S.ClosedAt (n + 1) (S.atom n ω ∩ E) :=
    S.closedAt_inter (S.closedAt_atom (Nat.le_succ n) ω) (S.closedAt_nextObs n _)
  rw [S.pr_eq_div, S.cexp_eq_div, S.cexp_eq_div, S.sum_cexp_regroup n hclosed (S.reach h) F]
  have hset : S.atom n ω ∩ E ∩ S.reach h = S.atom n ω ∩ S.reach h := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.2 hrE]
  rw [hset]
  have hsum : ∀ ω'' ∈ S.atom n ω ∩ S.reach h,
      S.ℙ.w ω'' * (S.ratio h n ω'' * F ω'') =
        (mass S.ℙ.w (S.atom n ω ∩ S.reach h) / mass S.ℙ.w (S.atom n ω)) *
          (S.ℙ.w ω'' * F ω'' *
            (mass S.ℙ.w (S.atom (n + 1) ω'') / mass S.ℙ.w (S.atom (n + 1) ω'' ∩ S.reach h))) := by
    intro ω'' hω''
    rw [Finset.mem_inter, S.mem_atom] at hω''
    unfold ratio
    rw [S.pr_eq_div, S.pr_eq_div, ← S.atom_eq_of_atomEq hω''.1,
      Finset.inter_comm (S.reach h) (S.atom n ω), Finset.inter_comm (S.reach h) (S.atom (n + 1) ω''),
      div_div_eq_mul_div]
    ring
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, Finset.inter_comm E (S.atom n ω)]
  field_simp

/-! ### Theorem 1 -/

/-- **Post 8 Theorem 1 (influence equals the expected score)**: on a smooth play space with full
support of the next observation (`AllPosObs`) and reachability of `h` from every positive atom along
it (`ReachPos h`), under Post 6's Assumption 3, Post 7's Assumption 4 and Post 8's Assumption 5 (the
named predicates `A3 h`, `A4 h`, `A5 h`), for every algorithm `A`, every `n ≤ |h|` and every
positive-mass world `ω` reaching `h`:
`𝕀^𝔼_{h₁:ₙ}(A, h)(ω) = 𝔼_{h₁:ₙ}[ f^n_{h,S̄_h}(A(h, S̄_h)) | h ](ω)`,
where `f^n` is applied to the *distribution* `A(h, S̄_h)` (Lemma 2 `fS_affine` makes this
`E_{a∼A(h,S̄_h)} f^n(a)`, the form `theorem1_sum` states). Proof: Post 8's downward induction, with
every "expectation shuffling" step a lemma of the finite play space (`IE_step_split`, `term1_eq`,
`term2_eq`, `pr_mul_cexp_cexp_eq`). A statement over all worlds, with junk conditionals, is false in
general: UDT1.01's score is junk at zero-probability worlds, harmlessly
([[udt-influence-101-findings]]).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 (udt-rep-082); mandate T4
Kind: C
Fidelity: exact on the support of `reach h`, with the two implicit positivity assumptions made explicit
Hyps: (a) `SmoothLaw` (theorem of the model of record); (a) `AllPosObs`, `ReachPos h` (regularity of
the play space, checked on the instances); (b) `A3 h` (Post 6 Assumption 3); (b) `A4 h` (Post 7
Assumption 4); (b) `A5 h` (Post 8 Assumption 5, in the time-`n`-precommitment form the proof uses) -/
theorem theorem1 (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA3 : S.A3 h) (hA4 : S.A4 h)
    (hA5 : S.A5 h) (hRP : S.ReachPos h) (A : Alg O Act Ξ N) :
    ∀ (n : ℕ), n ≤ h.1.val → ∀ ω, 0 < S.ℙ.w ω → ω ∈ S.reach h →
      S.IE n A h ω = S.cexp S.ℙ.w n (S.reach h) (fun ω' => S.fS h (S.play A h ω') n ω') ω := by
  suffices key : ∀ k n, n + k = h.1.val → ∀ ω, 0 < S.ℙ.w ω → ω ∈ S.reach h →
      S.IE n A h ω = S.cexp S.ℙ.w n (S.reach h) (fun ω' => S.fS h (S.play A h ω') n ω') ω by
    intro n hn ω hω hr
    exact key (h.1.val - n) n (by omega) ω hω hr
  intro k
  induction k with
  | zero =>
    intro n hn ω hω hr
    have hnlt : ¬ n < h.1.val := by omega
    have hnN : n < N := by have := h.1.isLt; omega
    have hpos : S.PosObs n ω := hall n hnN ω hω
    rw [S.lemma1_split hS hnN hpos]
    obtain ⟨h3P, h3E⟩ := hA3 n (by omega) A ω hω hr
    have hA3' : ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n A h o ω +
        S.IP n A h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω) =
        ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n (S.avg A h n) h o ω +
          S.IP n (S.avg A h n) h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω) :=
      Finset.sum_congr rfl fun o _ => by rw [h3P o, h3E o (fun hlt => absurd hlt hnlt)]
    rw [hA3', S.term1_eq hA5 A (by omega) hω hr]
    exact S.cexp_congr_on fun ω' _ => by rw [S.fS_of_ge h _ hnlt]
  | succ k ih =>
    intro n hn ω hω hr
    have hlt : n < h.1.val := by omega
    have hnN : n < N := lt_trans hlt h.1.isLt
    have hpos : S.PosObs n ω := hall n hnN ω hω
    rw [S.IE_step_split hS hA3 hA4 A hlt hω hr hpos, S.term1_eq hA5 A hlt.le hω hr,
      S.term2_eq hS hall hA5 A hlt hω hr]
    have hterm3 : S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hlt⟩)) ω *
        S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hlt⟩)) (fun ω' => S.IE (n + 1) A h ω') ω =
        S.cexp S.ℙ.w n (S.reach h)
          (fun ω' => S.ratio h n ω' * S.fS h (S.play A h ω') (n + 1) ω') ω := by
      rw [← S.pr_mul_cexp_cexp_eq hlt hω hr]
      congr 1
      refine S.cexp_congr_on_pos fun ω' hω' hω'0 => ?_
      rw [Finset.mem_inter, S.mem_atom] at hω'
      -- `ω'` agrees with `h` up to time `n + 1`, so its time-`(n+1)` atom can reach `h`
      have hagree : ∀ i : Fin N, (hi : i.val < n + 1) →
          S.obs ω' i = h.2 ⟨i.val, lt_of_lt_of_le hi hlt⟩ := by
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · rw [← hω'.1.1 i hi', S.obs_eq_of_reach hr i (lt_trans hi' hlt)]
        · have hi'' : i = ⟨n, hnN⟩ := Fin.ext hi'
          subst hi''
          exact (S.mem_nextObs hnN).1 hω'.2
      obtain ⟨ω'', hω''mem, hω''pos⟩ := exists_pos_of_mass_pos (hRP (n + 1) hlt ω' hω'0 hagree)
      rw [Finset.mem_inter, S.mem_atom] at hω''mem
      rw [S.IE_measAt (n + 1) A h ω' ω'' hω''mem.1, ih (n + 1) (by omega) ω'' hω''pos hω''mem.2,
        S.cexp_measAt S.ℙ.w (n + 1) (S.reach h) _ ω' ω'' hω''mem.1]
    rw [hterm3, ← S.cexp_sub, ← S.cexp_add]
    exact S.cexp_congr_on fun ω' _ => by rw [S.fS_of_lt h _ hlt]

/-- **Theorem 1 in Post 8's "E_{a∼A(h,S̄_h)}" form**: the influence is the conditional expectation,
given `h`, of the `A(h, S̄_h)`-average of the pure-action scores (Theorem 1 plus Lemma 2).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 and Theorem 2's first display
Kind: C
Fidelity: exact
Hyps: as `theorem1` -/
theorem theorem1_sum (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA3 : S.A3 h)
    (hA4 : S.A4 h) (hA5 : S.A5 h) (hRP : S.ReachPos h) (A : Alg O Act Ξ N) {n : ℕ} (hn : n ≤ h.1.val)
    {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    S.IE n A h ω = S.cexp S.ℙ.w n (S.reach h)
      (fun ω' => ∑ a, (S.play A h ω').w a * S.fS h (FinDist.delta a) n ω') ω := by
  rw [S.theorem1 hS hall hA3 hA4 hA5 hRP A n hn ω hω hr]
  exact S.cexp_congr_on_pos fun ω' hω' hω'0 =>
    S.fS_affine hS hall hA5 _ n hn ω' hω'0 (Finset.mem_inter.1 hω').2

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
