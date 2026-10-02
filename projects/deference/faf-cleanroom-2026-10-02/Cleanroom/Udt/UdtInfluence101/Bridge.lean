import Cleanroom.Udt.UdtInfluence101.ProfileLemmas
import Cleanroom.Udt.UdtInfluence101.Witnesses
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The bridge claims (T8): Assumption 3 versus decision-determination; Assumption 2 versus DD

Repair round 1 (2026-10-02). The corpus says "Assumption 3 *is* decision-determination" and
"Assumption 2 is a consequence of DD" ([[topics/decision-determination]] ll. 111–121; udt-rep-086,
2-002(a)). This module settles the two directions of the first and the second:

* **A DD-like environment implies A3** (`profile_env_implies_A3`): in every profile model the
  environment reads the algorithm only through its profile at the designated node and the realized
  causal past, and `ProfileModel.A3` derives Assumption 3 from that — the honest sentence.
* **A3 does not imply a DD-like environment** (`law_not_determined`, `A3_sq`): the play space
  `sqSpace` has an ε-law that reads the algorithm's *code* — its action at an unrealized epistemic
  state — through a second-order term `ε² · c(A)`, so two algorithms with identical behaviour on every
  world have different ε-laws; yet every influence there is a derivative at `0` of a function with
  vanishing first-order term, so Assumption 3 holds (as `0 = 0`). Assumption 3 is a first-order
  statement about derivatives, not an exact conditional independence: calling it "decision-
  determination" is a category error.
* **Assumption 2 needs no DD at all** (`a2_without_dd`): the law of total expectation over the next
  observation holds in `sqSpace` — a code-reading environment — as in every play space
  (`cexp_eq_sum_nextObs_prior`).
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Home (fair fair_w)

namespace Bridge

noncomputable section

/-- **A DD-like environment implies Assumption 3**: in every profile model — where the environment
sees the algorithm only through its profile at `pn m` and the realized actions — Assumption 3 holds
at every node. (The bridge udt-rep-086 asks for, restated from `ProfileModel.A3`; an alias of that
theorem, so Kind `L`.)
Source: [[topics/decision-determination]] ll. 111–121 (udt-rep-086); mandate T8(a)
Kind: L
Fidelity: exact (the forward direction, in the model of record)
Hyps: (a) none -/
theorem profile_env_implies_A3 {O Act Ξ W : Type} [Fintype O] [DecidableEq O] [Fintype Act]
    [DecidableEq Act] [Fintype Ξ] [DecidableEq Ξ] [Fintype W] [DecidableEq W] {N : ℕ}
    (M : ProfileModel O Act Ξ W N) (h : Node O N) : M.toPlaySpace.A3 h := M.A3 h

/-! ### A play space whose law reads the algorithm's code, satisfying Assumption 3 -/

/-- The only node of the horizon-`1` tree.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def h₀ : Node Bool 1 := ⟨0, ![]⟩

/-- An unrealized epistemic state at `h₀` (every world's state is `true`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def s₁ : Fin 1 → Bool := ![false]

/-- The code-reading coefficient: half the deviation from `1/2` of the probability `A` puts on `true`
at the unrealized state `s₁`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def cA (A : Alg Bool Bool Bool 1) : ℝ := ((A h₀ s₁).w true - 1 / 2) / 2

/-- Supporting lemma `w_le_one`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_le_one (μ : FinDist Bool) (b : Bool) : μ.w b ≤ 1 := by
  rw [← μ.sum_one]
  exact Finset.single_le_sum (fun a _ => μ.nonneg a) (Finset.mem_univ b)

/-- Supporting lemma `cA_bounds`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cA_bounds (A : Alg Bool Bool Bool 1) : -(1 / 4) ≤ cA A ∧ cA A ≤ 1 / 4 := by
  unfold cA
  have h0 := (A h₀ s₁).nonneg true
  have h1 := w_le_one (A h₀ s₁) true
  constructor <;> linarith

/-- The second-order ε-law: the fair prior plus `ε² · c(A) · (±1)`.
Source: mandate T8(a) ("a second-order dependence that vanishes at `ε = 0`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def sqLaw (A : Alg Bool Bool Bool 1) (_h : Node Bool 1) (ε : ℝ) (ω : Bool) : ℝ :=
  1 / 2 + ε ^ 2 * (cA A * (if ω then 1 else -1))

/-- **The code-reading play space**: two worlds, fair prior, one observation (the world), constant
states, utility `[ω = true]`, and the ε-law `sqLaw`.
Source: mandate T8(a)
Kind: D
Fidelity: n/a (a counter-model)
Hyps: n/a -/
def sqSpace : PlaySpace Bool Bool Bool 1 Bool where
  ℙ := fair
  obs := fun ω _ => ω
  states := fun _ _ => true
  U := fun ω => if ω then 1 else 0
  law := sqLaw
  law_zero := fun _ _ => by funext ω; simp [sqLaw]
  law_nonneg := fun A _ ε h0 h1 ω => by
    obtain ⟨hc1, hc2⟩ := cA_bounds A
    have hε : ε ^ 2 ≤ 1 := by nlinarith
    have hε0 : 0 ≤ ε ^ 2 := sq_nonneg ε
    unfold sqLaw
    cases ω <;> simp <;> nlinarith
  law_sum := fun _ _ ε => by
    simp [Fintype.sum_bool, sqLaw]
    ring

/-- Supporting lemma `hasDerivAt_sqLaw` (the ε-law has zero derivative at `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_sqLaw (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (ω : Bool) :
    HasDerivAt (fun ε => sqLaw A h ε ω) 0 0 := by
  have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (cA A * (if ω then 1 else -1))).const_add (1 / 2)
  simpa [sqLaw] using this

/-- **`sqSpace` is smooth.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem smoothLaw_sq : sqSpace.SmoothLaw := fun A h ω => ⟨0, hasDerivAt_sqLaw A h ω⟩

/-- Supporting lemma `deriv_sqLaw`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem deriv_sqLaw (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (ω : Bool) :
    deriv (fun ε => sqSpace.law A h ε ω) 0 = 0 := (hasDerivAt_sqLaw A h ω).deriv

/-- Supporting lemma `dmass_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dmass_zero (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (E : Finset Bool) :
    sqSpace.dmass A h E = 0 := Finset.sum_eq_zero fun ω _ => deriv_sqLaw A h ω

/-- Supporting lemma `dwsum_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dwsum_zero (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (E : Finset Bool) (f : Bool → ℝ) :
    sqSpace.dwsum A h E f = 0 := Finset.sum_eq_zero fun ω _ => by rw [deriv_sqLaw, zero_mul]

/-- Supporting lemma `ℙ_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ℙ_pos (ω : Bool) : 0 < sqSpace.ℙ.w ω := by
  show 0 < fair.w ω
  rw [fair_w]; norm_num

/-- **Every influence on probability in `sqSpace` is zero.**
Source: mandate T8(a)
Kind: L
Fidelity: exact
Hyps: none -/
theorem IP_zero (n : ℕ) (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (o ω : Bool) :
    sqSpace.IP n A h o ω = 0 := by
  unfold PlaySpace.IP
  have hatom : 0 < mass sqSpace.ℙ.w (sqSpace.atom n ω) :=
    mass_pos_of_mem sqSpace.ℙ.nonneg (sqSpace.self_mem_atom n ω) (ℙ_pos ω)
  rw [(sqSpace.hasDerivAt_pr smoothLaw_sq A h hatom _).deriv, dmass_zero, dmass_zero]
  simp

/-- **Every influence on conditional expected utility in `sqSpace` is zero.**
Source: mandate T8(a)
Kind: L
Fidelity: exact
Hyps: none -/
theorem IEo_zero (n : ℕ) (A : Alg Bool Bool Bool 1) (h : Node Bool 1) (o ω : Bool) :
    sqSpace.IEo n A h o ω = 0 := by
  unfold PlaySpace.IEo
  rcases (sqSpace.atom n ω ∩ sqSpace.nextObs n o).eq_empty_or_nonempty with hE | ⟨ω', hω'⟩
  · have : (fun ε => sqSpace.cexp (sqSpace.law A h ε) n (sqSpace.nextObs n o) sqSpace.U ω) =
        fun _ => 0 := by
      funext ε
      unfold PlaySpace.cexp
      rw [hE]
      simp [condExpJunk, mass]
    rw [this, deriv_const]
  · have hpos : 0 < mass sqSpace.ℙ.w (sqSpace.atom n ω ∩ sqSpace.nextObs n o) :=
      mass_pos_of_mem sqSpace.ℙ.nonneg hω' (ℙ_pos ω')
    rw [(sqSpace.hasDerivAt_cexp smoothLaw_sq A h hpos _).deriv, dwsum_zero, dmass_zero]
    simp

/-- **Assumption 3 holds in `sqSpace`** (every influence is zero, so both sides of each clause are
`0`).
Source: mandate T8(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem A3_sq (h : Node Bool 1) : sqSpace.A3 h := by
  intro n _ A ω _ _
  exact ⟨fun o => by rw [IP_zero, IP_zero], fun o _ => by rw [IEo_zero, IEo_zero]⟩

/-- The algorithm that plays `false` at the unrealized state `s₁` and `true` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def A₂ : Alg Bool Bool Bool 1 := fun _ s =>
  if s ⟨0, Nat.succ_pos _⟩ = false then FinDist.delta false else FinDist.delta true

/-- Supporting lemma `states_eq` (every state of every world is `true`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem states_eq (ω : Bool) (i : Fin 2) : sqSpace.states ω i = true := rfl

/-- Supporting lemma `play_eq` (`ofAct true` and `A₂` behave identically on every world).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_eq (ω : Bool) : sqSpace.play (ofAct true) h₀ ω = sqSpace.play A₂ h₀ ω := by
  show FinDist.delta true = A₂ h₀ (sqSpace.statesAlong ω h₀)
  simp [A₂, PlaySpace.statesAlong, states_eq]

/-- **Assumption 3 does not say the environment is a function of the algorithm's behaviour**: in
`sqSpace`, which satisfies Assumption 3 at every node, two algorithms with the same action on every
world (hence the same profile under any prior) have different ε-laws.
Source: [[topics/decision-determination]] ll. 111–121 (udt-rep-086: "Assumption 3 *is* DD"); mandate T8(a) (the converse)
Kind: P
Fidelity: exact (the counter-model; "same behaviour" is pointwise equality of `play` on worlds)
Hyps: none -/
theorem law_not_determined : ∃ A₁ A₂ : Alg Bool Bool Bool 1,
    (∀ ω, sqSpace.play A₁ h₀ ω = sqSpace.play A₂ h₀ ω) ∧ sqSpace.law A₁ h₀ 1 ≠ sqSpace.law A₂ h₀ 1 := by
  refine ⟨ofAct true, A₂, play_eq, fun heq => ?_⟩
  have := congrFun heq true
  change sqLaw (ofAct true) h₀ 1 true = sqLaw A₂ h₀ 1 true at this
  simp [sqLaw, cA, A₂, s₁, ofAct, ofDist] at this

/-- **Assumption 2 holds in a code-reading environment**: the law of total expectation over the next
observation in `sqSpace`, whose ε-law depends on the algorithm beyond its behaviour on worlds. The
corpus's "Assumption 2 is a consequence of DD" is vacuously true and wrongly explained: no
DD-flavoured hypothesis enters (`cexp_eq_sum_nextObs_prior` holds in every play space).
Source: [[topics/decision-determination]] l. 117; mandate T8(b)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem a2_without_dd (n : ℕ) (hn : n < 1) (ω : Bool) (f : Bool → ℝ) :
    sqSpace.cexp sqSpace.ℙ.w n univ f ω =
      ∑ o, sqSpace.pr sqSpace.ℙ.w n (sqSpace.nextObs n o) ω *
        sqSpace.cexp sqSpace.ℙ.w n (sqSpace.nextObs n o) f ω :=
  sqSpace.cexp_eq_sum_nextObs_prior hn ω f

end

end Bridge

end Cleanroom.Udt.UdtInfluence101
