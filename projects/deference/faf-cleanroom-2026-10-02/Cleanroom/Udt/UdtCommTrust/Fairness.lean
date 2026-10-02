import Cleanroom.Udt.UdtCommTrust.Concrete

/-!
# `Cleanroom.Udt.UdtCommTrust.Fairness`: the fairness conjunction and `P(Π̈ = R) = 1` (T15(a))

Work package `udt-comm-trust`, target T15(a) (udt-rep-2-011(a)), first half, written in repair
round 1. The question: does `DecisionDetermined ∧ HasCA ∧ (∀ r ∈ range R, Stable r) ∧ UdtRule`
yield the self-esteem condition `P(Π̈ = R) = 1`? The findings' verdict was: yes when the
recommendation is constant, by `HasCA` alone; no for a two-valued recommendation (an eight-world
design, still unverified). This module proves the first half, and slightly more: communicative
alternatives *at a single input* suffice, and neither decision-determination nor stability nor
the UDT rule is used.
-/

namespace Cleanroom.Udt.UdtCommTrust

namespace ConcreteDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [DecidableEq AI] [Fintype DI] [DecidableEq DI] [Fintype DE] [DecidableEq DE] [Fintype DB]
  [DecidableEq DB]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- **With a constant recommendation, communicative alternatives at one input force
`P(Π̈ = R) = 1`** (T15(a), the positive half). If `R ≡ r` and every attained action at `(ȯ, ö)` has a
communicative alternative, then every world's external policy follows `r`. Proof: for a world
`ω`, let `π̈ = Π̈(ω)` and `a = Π*(ω)(ȯ, ö)` (attained); the CA identity at `a` gives
`P(Π̈ = π̈ ∣ Π*(ȯ,ö) = a) = P(Π̈ = π̈ ∣ Π*(ȯ,ö) = c, Π̈ = R)`; if `π̈` did not follow `r` the right
conditioning event would meet `{Π̈ = π̈}` in nothing (on `{Π̈ = R}` every policy follows `r`), so
the right side is `0` (junk or genuine), the left side is `0`, and `{Π̈ = π̈} ∩ {Π*(ȯ,ö) = a}` is
empty — but it contains `ω`. So the fairness conjunction's CA clause alone yields the self-esteem
condition when the recommendation is constant; DD, stability and the UDT rule play no role. For a
two-valued recommendation the findings' eight-world design (unverified) says the implication
fails; that half is open.
Source: mandate T15(a) (udt-rep-2-011(a)); findings, T15
Kind: P
Fidelity: stronger: CA at one input, no DD/stability/rule
Hyps: (a); §3 (c) junk `0` (the empty right-hand event scores `0` either way) -/
theorem followsR_of_hasCA_const (r : OE → Option AE) (hconst : ∀ ω, S.R ω = r)
    (o : OI) (e : OE) (hCA : ∀ a, (S.evS o e a).Nonempty → ∃ c, S.IsCA o e a c) :
    mass S.μ.w S.evFollowsR = 1 := by
  rw [S.evFollowsR_eq_univ_iff, Finset.eq_univ_iff_forall]
  intro ω
  rw [mem_evFollowsR, hconst ω]
  by_contra hnf
  have hne : (S.evS o e (S.polS ω (o, e))).Nonempty := S.evS_self_nonempty ω o e
  obtain ⟨c, hc⟩ := hCA _ hne
  have h := hc.2 (S.polE ω)
  have hempty : S.evPolE (S.polE ω) ∩ (S.evS o e c ∩ S.evFollowsR) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ω' hω'
    have h1 : S.polE ω' = S.polE ω := by
      have := (Finset.mem_inter.1 hω').1
      simpa [AbstractDS.evPolE] using this
    have h2 : ω' ∈ S.evFollowsR := (Finset.mem_inter.1 (Finset.mem_inter.1 hω').2).2
    rw [mem_evFollowsR, h1, hconst ω'] at h2
    exact hnf h2
  have hrhs : condProbJunk S.μ.w (S.evPolE (S.polE ω)) (S.evS o e c ∩ S.evFollowsR) 0 = 0 := by
    by_cases hF : (S.evS o e c ∩ S.evFollowsR).Nonempty
    · rw [condProbJunk_of_nonempty S.pos hF, hempty]
      simp [mass]
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      rw [hF]
      exact condProbJunk_of_empty _ _
  rw [hrhs, condProbJunk_of_nonempty S.pos hne, div_eq_zero_iff] at h
  rcases h with h | h
  · rw [mass_eq_zero_iff S.pos] at h
    have hmem : ω ∈ S.evPolE (S.polE ω) ∩ S.evS o e (S.polS ω (o, e)) :=
      Finset.mem_inter.2 ⟨by simp [AbstractDS.evPolE], by simp⟩
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem
  · exact absurd h (mass_pos_of_nonempty S.pos hne).ne'

/-- **The fairness conjunction with a constant recommendation gives `P(Π̈ = R) = 1`**: the
corollary of `followsR_of_hasCA_const` with the conjunction's `HasCA` (and its other clauses
unused, as explicit binders so the docstring can say so).
Source: mandate T15(a) (udt-rep-2-011(a))
Kind: C
Fidelity: exact for the constant-`R` case of the conjecture; DD, stability and the rule are unused binders
Hyps: (a); §3 (c) -/
theorem followsR_of_fairness_const [Nonempty OI] [Nonempty OE] (r : OE → Option AE)
    (hconst : ∀ ω, S.R ω = r) (_hDD : S.DecisionDetermined) (hCA : S.HasCA)
    (_hStab : ∀ r ∈ Set.range S.R, S.Stable r) (_hUdt : S.UdtRule) :
    mass S.μ.w S.evFollowsR = 1 :=
  S.followsR_of_hasCA_const r hconst (Classical.arbitrary OI) (Classical.arbitrary OE)
    fun a ha => hCA _ _ a ha

end ConcreteDS

end Cleanroom.Udt.UdtCommTrust
