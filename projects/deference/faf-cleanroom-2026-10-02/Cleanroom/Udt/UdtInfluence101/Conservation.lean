import Cleanroom.Udt.UdtInfluence101.Calculus

/-!
# `Cleanroom.Udt.UdtInfluence101.Conservation`: why Conservation of Expected Influence fails

Target T6 of [[udt-influence-101-mandate]]. The **decomposition theorem** `IEo_decomp`: for every
smooth play space, at a positive event `E = atom_n ∩ {h_{n+1}}` all of whose time-`(n+1)` atoms are
positive,

`𝕀^𝔼_{h₁:ₙ}(A, h, h_{n+1}) − 𝔼_{h₁:ₙ}[𝕀^𝔼_{h₁:ₙ₊₁}(A, h) | h_{n+1}] = Σ_{ω' ∈ E} (d/dε ℙ^ε(ω' | E))|₀ · 𝔼_{h₁:ₙ₊₁}[U](ω')`.

Grouping the worlds by their time-`(n+1)` atoms, the right-hand side is
`Σ_α (d/dε ℙ^ε_{h₁:ₙ}(α | h_{n+1}))|₀ · 𝔼_α[U]`: CEI fails exactly when ε-play shifts the conditional
law of the next unplannable state and that shift correlates with the next-state expected utility —
the run's precise form of Post 7 §2.1's "implicit update on your unplannables". Corollaries: `CEI`
holds iff the shift term vanishes (`CEI_iff`); Post 7's Assumption 4 holds at `(n, ω)` whenever the
shift term is the same for `A` and its average `Ā_{h,n}` (`A4_at_of_shift_eq`), which is how the
model of record discharges it.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Filter Topology Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-- **The tower identity for an arbitrary weight function** on an `𝔽_{n+1}`-closed set all of whose
time-`(n+1)` atoms are non-null: `Σ_{ω' ∈ A} w(ω') 𝔼^w_{n+1}[f](ω') = Σ_{ω' ∈ A} w(ω') f(ω')`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_condExpJunk_tower (w : Ω → ℝ) (n : ℕ) {A : Finset Ω} (hA : S.ClosedAt (n + 1) A)
    (hne : ∀ ω' ∈ A, mass w (S.atom (n + 1) ω') ≠ 0) (f : Ω → ℝ) :
    ∑ ω' ∈ A, w ω' * condExpJunk w f (S.atom (n + 1) ω') 0 = ∑ ω' ∈ A, w ω' * f ω' := by
  simp only [condExpJunk_eq_div]
  have hinner : ∀ ω' ∈ A, w ω' * ((∑ ω'' ∈ S.atom (n + 1) ω', w ω'' * f ω'') /
      mass w (S.atom (n + 1) ω')) =
      ∑ ω'' ∈ A, if S.AtomEq (n + 1) ω' ω'' then
        w ω' * (w ω'' * f ω'' / mass w (S.atom (n + 1) ω'')) else 0 := by
    intro ω' hω'
    have hset : A.filter (fun ω'' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω' := by
      ext ω''
      simp only [Finset.mem_filter, S.mem_atom]
      exact ⟨fun h => h.2, fun h => ⟨hA ω' hω' ω'' h, h⟩⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω'' hω'' => ?_
    rw [S.mem_atom] at hω''
    rw [S.atom_eq_of_atomEq hω'', div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' hω'' => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : A.filter (fun ω' => S.AtomEq (n + 1) ω' ω'') = S.atom (n + 1) ω'' := by
    ext ω'
    simp only [Finset.mem_filter, S.mem_atom]
    exact ⟨fun h => S.atomEq_symm h.2, fun h => ⟨hA ω'' hω'' ω' h, S.atomEq_symm h⟩⟩
  rw [hset, ← Finset.sum_mul]
  have hm : (∑ ω' ∈ S.atom (n + 1) ω'', w ω') = mass w (S.atom (n + 1) ω'') := rfl
  rw [hm, mul_div_assoc', mul_comm (mass w _), mul_div_assoc, div_self (hne ω'' hω''), mul_one]

/-- The derivative at `0` of the **conditional weight** `law_ε(ω') / law_ε(E)` of a world given an
event, under ε-play of `A` at `h`: the shift of the conditional law that ε-play induces.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.1 ("implicit update on your unplannables"); mandate T6(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dcw (A : Alg O Act Ξ N) (h : Node O N) (E : Finset Ω) (ω' : Ω) : ℝ :=
  deriv (fun ε => S.law A h ε ω' / mass (S.law A h ε) E) 0

/-- Supporting lemma `hasDerivAt_condWeight`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_condWeight (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) {E : Finset Ω}
    (hpos : 0 < mass S.ℙ.w E) (ω' : Ω) :
    HasDerivAt (fun ε => S.law A h ε ω' / mass (S.law A h ε) E)
      ((deriv (fun ε => S.law A h ε ω') 0 * mass S.ℙ.w E - S.ℙ.w ω' * S.dmass A h E) /
        (mass S.ℙ.w E) ^ 2) 0 := by
  obtain ⟨c, hc⟩ := hS A h ω'
  have hm := S.hasDerivAt_mass hS A h E
  have h0 : mass (S.law A h 0) E = mass S.ℙ.w E := by rw [S.law_zero]
  have hdiv := hc.div hm (by rw [h0]; exact hpos.ne')
  simp only [S.law_zero] at hdiv
  rw [hc.deriv]
  exact hdiv

/-- Supporting lemma `eventually_cexp_eq_sum_tower` (along the ε-family near `0`, the conditional
expectation of `U` given `E` is the conditional-weight average of the time-`(n+1)` conditional
expectations).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eventually_cexp_eq_sum_tower (hS : S.SmoothLaw) {n : ℕ} {ω : Ω} (o : O)
    (hE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o))
    (hatoms : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n o, 0 < mass S.ℙ.w (S.atom (n + 1) ω'))
    (A : Alg O Act Ξ N) (h : Node O N) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), S.cexp (S.law A h ε) n (S.nextObs n o) S.U ω =
      ∑ ω' ∈ S.atom n ω ∩ S.nextObs n o,
        (S.law A h ε ω' / mass (S.law A h ε) (S.atom n ω ∩ S.nextObs n o)) *
          S.cexp (S.law A h ε) (n + 1) univ S.U ω' := by
  have hall : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ ω' ∈ S.atom n ω ∩ S.nextObs n o,
      0 < mass (S.law A h ε) (S.atom (n + 1) ω') := by
    rw [Filter.eventually_all_finset]
    intro ω' hω'
    exact S.eventually_mass_pos hS A h (hatoms ω' hω')
  filter_upwards [hall, S.eventually_mass_pos hS A h hE] with ε hε hεE
  have hclosed : S.ClosedAt (n + 1) (S.atom n ω ∩ S.nextObs n o) :=
    S.closedAt_inter (S.closedAt_atom (Nat.le_succ n) ω) (S.closedAt_nextObs n o)
  simp only [cexp, Finset.inter_univ]
  rw [condExpJunk_eq_div, ← S.sum_condExpJunk_tower (S.law A h ε) n hclosed
    (fun ω' hω' => (hε ω' hω').ne') S.U, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- **The decomposition behind the failure of Conservation of Expected Influence**: on a smooth play
space, at a time-`n` atom and observation `o` whose event `E = atom_n ∩ {o}` is positive with all its
time-`(n+1)` atoms positive,
`𝕀^𝔼_{h₁:ₙ}(A,h,o) = 𝔼_{h₁:ₙ}[𝕀^𝔼_{h₁:ₙ₊₁}(A,h) | o] + Σ_{ω' ∈ E} (d/dε ℙ^ε(ω' | E))|₀ · 𝔼_{h₁:ₙ₊₁}[U](ω')`.
The second term — grouped by time-`(n+1)` atoms `α`, `Σ_α (d/dε ℙ^ε_{h₁:ₙ}(α | o))|₀ · 𝔼_α[U]` — is
the "implicit update on your unplannables": CEI fails exactly when ε-play shifts the conditional
law of the next unplannable state and that shift correlates with the next-state expected utility.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.1 (udt-rep-085); mandate T6(b)
Kind: P
Fidelity: exact (finite form, for any observation `o`; Post 7 states CEI for `o = h_{n+1}`)
Hyps: (a) `SmoothLaw`; (a) positivity of `E` and of its time-`(n+1)` atoms (regularity) -/
theorem IEo_decomp (hS : S.SmoothLaw) {n : ℕ} {ω : Ω} (o : O)
    (hE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o))
    (hatoms : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n o, 0 < mass S.ℙ.w (S.atom (n + 1) ω'))
    (A : Alg O Act Ξ N) (h : Node O N) :
    S.IEo n A h o ω = S.cexp S.ℙ.w n (S.nextObs n o) (fun ω' => S.IE (n + 1) A h ω') ω +
      ∑ ω' ∈ S.atom n ω ∩ S.nextObs n o,
        S.dcw A h (S.atom n ω ∩ S.nextObs n o) ω' * S.cexp S.ℙ.w (n + 1) univ S.U ω' := by
  set E := S.atom n ω ∩ S.nextObs n o with hEdef
  have hd : HasDerivAt (fun ε => ∑ ω' ∈ E,
      (S.law A h ε ω' / mass (S.law A h ε) E) * S.cexp (S.law A h ε) (n + 1) univ S.U ω')
      (∑ ω' ∈ E, (S.dcw A h E ω' * S.cexp S.ℙ.w (n + 1) univ S.U ω' +
        (S.ℙ.w ω' / mass S.ℙ.w E) * S.IE (n + 1) A h ω')) 0 := by
    apply HasDerivAt.fun_sum
    intro ω' hω'
    have h1 := S.hasDerivAt_condWeight hS A h hE ω'
    have h2 := S.hasDerivAt_cexp hS A h (E := univ) (n := n + 1) (ω := ω')
      (by rw [Finset.inter_univ]; exact hatoms ω' hω') S.U
    have h12 := h1.mul h2
    simp only [S.law_zero] at h12
    rw [← h1.deriv, ← h2.deriv] at h12
    exact h12
  rw [IEo, Filter.EventuallyEq.deriv_eq (S.eventually_cexp_eq_sum_tower hS o hE hatoms A h), hd.deriv,
    Finset.sum_add_distrib, add_comm]
  congr 1
  rw [S.cexp_eq_div, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- **CEI holds iff the unplannable shift term vanishes** (Post 7 §2.1's "dream scenario", with the
exact obstruction).
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.1 (udt-rep-085)
Kind: P
Fidelity: exact
Hyps: as `IEo_decomp` -/
theorem CEI_iff (hS : S.SmoothLaw) {h : Node O N} {n : ℕ} (hn : n < h.1.val) {ω : Ω}
    (hE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)))
    (hatoms : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩), 0 < mass S.ℙ.w (S.atom (n + 1) ω'))
    (A : Alg O Act Ξ N) :
    S.CEI n A h ω ↔
      ∑ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩),
        S.dcw A h (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) ω' * S.cexp S.ℙ.w (n + 1) univ S.U ω' = 0 := by
  unfold CEI
  constructor
  · intro hc
    have := hc hn
    rw [S.IEo_decomp hS _ hE hatoms A h] at this
    linarith
  · intro hz hn'
    rw [S.IEo_decomp hS _ hE hatoms A h, hz, add_zero]

/-- **Post 7's Assumption 4 at `(n, ω)` from equal unplannable shifts**: if ε-playing `A` and
ε-playing its average `Ā_{h,n}` shift the conditional law of every world below `h_{n+1}` identically,
then the entanglement gap is conserved in expectation (the CEG identity at `(n, ω)`). This is how the
model of record discharges Assumption 4: the shift depends on the algorithm only through its
profile, which `Ā_{h,n}` shares with `A`.
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4 and §2.8 ("the diffuse influence component is the same between A and Ā_{h,n}"); mandate T6(a), T7
Kind: C
Fidelity: exact
Hyps: as `IEo_decomp`, plus the equal-shift hypothesis -/
theorem A4_at_of_shift_eq (hS : S.SmoothLaw) {h : Node O N} {n : ℕ} (hn : n < h.1.val) {ω : Ω}
    (hE : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)))
    (hatoms : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩), 0 < mass S.ℙ.w (S.atom (n + 1) ω'))
    (A : Alg O Act Ξ N)
    (hshift : ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩),
      S.dcw A h (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) ω' =
        S.dcw (S.avg A h n) h (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) ω') :
    S.IEo n A h (h.2 ⟨n, hn⟩) ω - S.IEo n (S.avg A h n) h (h.2 ⟨n, hn⟩) ω =
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩))
        (fun ω' => S.IE (n + 1) A h ω' - S.IE (n + 1) (S.avg A h n) h ω') ω := by
  rw [S.IEo_decomp hS _ hE hatoms A h, S.IEo_decomp hS _ hE hatoms (S.avg A h n) h, S.cexp_sub,
    Finset.sum_congr rfl fun ω' hω' => by rw [hshift ω' hω']]
  ring

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
