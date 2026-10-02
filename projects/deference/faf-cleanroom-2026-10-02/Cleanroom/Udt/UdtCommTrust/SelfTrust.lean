import Cleanroom.Udt.UdtCommTrust.Concrete

/-!
# `Cleanroom.Udt.UdtCommTrust.SelfTrust`: Communicative Expectation and Self-Trust

Work package `udt-comm-trust`, targets T10 (the Communicative Expectation lemma, as proved and as
printed), T11 (Self-Trust: the printed display is a tautology; the repaired theorem) and T17(ii)
(the strict-argmax ceiling). Sources: [[communication-trust-translated]] lines 458–486; the original
`references/communication&trust.md` lines 468–494 (the proof's `≤`).

The engine is T7's decomposition over external policies (`AbstractDS.decomposition`), generalised
here to any non-empty `D_{I,B}`-measurable event (`decomposition_of_measurable`). Applying it to
`{Π*(ȯ,ö) = c} ∩ {Π̈ = R}` needs that event to be `D_{I,B}`-measurable, which holds when the
recommendation is a function of the agent's dynamics (`IsSubvariable S.DIB S.R`) — a hypothesis
the paper's proof uses without stating (findings, T10).
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [Fintype DE] [DecidableEq DE] [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]

namespace AbstractDS

variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **The decomposition over external policies on any non-empty `D_{I,B}`-measurable event**:
under DD, `E[U ∣ G] = ∑_{π̈ ∈ range Π̈} E[U ∣ Π̈ = π̈] · P(Π̈ = π̈ ∣ G)`. T7's `decomposition` is the
case `G = {Π*(ȯ,ö) = a}`; T10 needs the case `G = {Π*(ȯ,ö) = c} ∩ {Π̈ = R}`.
Source: [[communication-trust-translated]] lines 463–466 (udt-rep-016, 019)
Kind: P
Fidelity: n/a (infrastructure for T10)
Hyps: (a); §3 (c) -/
theorem decomposition_of_measurable (h : S.DecisionDetermined) {G : Finset Ω} (hG : G.Nonempty)
    (hmeas : ∀ ω ∈ G, ∀ ω', S.DIB ω' = S.DIB ω → ω' ∈ G) :
    condExpJunk S.μ.w S.U G (-1) = ∑ π ∈ Finset.univ.image S.polE,
      S.policyUtility π * condProbJunk S.μ.w (S.evPolE π) G 0 := by
  rw [condExpJunk_total S.pos S.U S.polE hG]
  have hzero : ∀ π ∈ (Finset.univ : Finset (OE → AE)), π ∉ Finset.univ.image S.polE →
      S.policyUtility π * condProbJunk S.μ.w (S.evPolE π) G 0 = 0 := by
    intro π _ hπ
    have : S.evPolE π = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      rw [mem_evPolE] at hω
      exact hπ (Finset.mem_image.2 ⟨ω, Finset.mem_univ _, hω⟩)
    rw [condProbJunk_of_nonempty S.pos hG, this, Finset.empty_inter]
    simp [mass]
  symm
  rw [Finset.sum_subset (Finset.subset_univ _) hzero]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hF : (G.filter fun ω => S.polE ω = π).Nonempty
  · congr 1
    refine (S.condExp_eq_policyUtility_of_measurable h hF ?_ π ?_).symm
    · intro ω hω ω' hω'
      rw [Finset.mem_filter] at hω ⊢
      exact ⟨hmeas ω hω.1 ω' hω', by rw [← hω.2]; exact S.polE_sub ω' ω hω'⟩
    · intro ω hω
      exact (Finset.mem_filter.1 hω).2
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    have this : condProbJunk S.μ.w (S.evPolE π) G 0 = 0 := by
      rw [condProbJunk_of_nonempty S.pos hG]
      unfold evPolE
      rw [event_inter_eq_filter, hF]
      simp [mass]
    have this' : condProbJunk S.μ.w (event fun ω => S.polE ω = π) G 0 = 0 := this
    rw [hF, this', this, mul_zero, mul_zero]

end AbstractDS

namespace ConcreteDS

variable [DecidableEq AI]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-! ### T10: Communicative Expectation -/

/-- **Communicative Expectation, as the proof proves it (T10(i))**: under DD, `Π* ⊑ D_{I,B}` and
`R ⊑ D_{I,B}`, if `c` is a communicative alternative to the attained action `a` at `(ȯ, ö)`, then
`E[U ∣ Π*(ȯ,ö) = a] = E[U ∣ Π*(ȯ,ö) = c, Π̈ = R]`. Both sides decompose over `Π̈` and the CA clause
matches the weights. The paper's lemma statement (translation line 458) has no `Π̈ = R` on the right;
its proof (line 466) does — this is the proof's statement.
Source: [[communication-trust-translated]] lines 458–470 (udt-rep-019); original lines 468–478
Kind: P
Fidelity: exact to the proof (the printed statement is `commExp_printed`)
Hyps: (a) throughout — `Π* ⊑ D_{I,B}` (T7) and `R ⊑ D_{I,B}` are hypotheses the paper's proof uses silently; §3 (c) -/
theorem commExp_proof (hDD : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    (hR : IsSubvariable S.DIB S.R) {o : OI} {e : OE} {a c : AI × AE} (hca : S.IsCA o e a c)
    (ha : (S.evS o e a).Nonempty) :
    S.score o e a = condExpJunk S.μ.w S.U (S.evS o e c ∩ S.evFollowsR) (-1) := by
  rw [S.decomposition hDD hsub ha,
    S.decomposition_of_measurable hDD (S.isCA_nonempty hca ha) ?_]
  · exact Finset.sum_congr rfl fun π _ => by rw [hca.2 π]
  · intro ω hω ω' hω'
    rw [Finset.mem_inter, AbstractDS.mem_evS, mem_evFollowsR] at hω ⊢
    refine ⟨?_, ?_⟩
    · rw [← hω.1]
      exact congrFun (hsub ω' ω hω') (o, e)
    · rw [S.polE_sub ω' ω hω', hR ω' ω hω']
      exact hω.2

/-- **Communicative Expectation, as printed (T10(ii))**: with the extra hypothesis `P(Π̈ = R) = 1`
(condition (3) of the Self-Trust theorem, which the paper lists only for the theorem), the right
side loses its `Π̈ = R`: `E[U ∣ Π*(ȯ,ö) = a] = E[U ∣ Π*(ȯ,ö) = c]`. The original's Self-Trust proof
(line ~484) writes `≤` where the lemma gives `=`.
Source: [[communication-trust-translated]] line 458 (udt-rep-019, 2-008(b))
Kind: P
Fidelity: exact to the statement, with the added hypothesis
Hyps: (a) `P(Π̈ = R) = 1` is one of the theorem's own conditions; the rest as `commExp_proof`; §3 (c) -/
theorem commExp_printed (hDD : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    (hR : IsSubvariable S.DIB S.R) (h1 : mass S.μ.w S.evFollowsR = 1) {o : OI} {e : OE}
    {a c : AI × AE} (hca : S.IsCA o e a c) (ha : (S.evS o e a).Nonempty) :
    S.score o e a = S.score o e c := by
  rw [S.commExp_proof hDD hsub hR hca ha, (S.evFollowsR_eq_univ_iff).1 h1, Finset.inter_univ]
  rfl

/-! ### T11: Self-Trust -/

variable [Fintype AI]

/-- The attained actions at `(ȯ, ö)`: the paper's `range A_ö`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def attained (o : OI) (e : OE) : Finset (AI × AE) := univ.filter fun a => (S.evS o e a).Nonempty

/-- Supporting lemma `mem_attained`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_attained {o : OI} {e : OE} {a : AI × AE} :
    a ∈ S.attained o e ↔ (S.evS o e a).Nonempty := by simp [attained]

/-- **Self-Trust as printed is a tautology (T11(a))**. Quoted (translation lines 472–478; the
original lines 480–486 is identical modulo notation): "If a concrete decision structure is (1)
decision-determined, (2) has communicative alternatives, and (3) has `P(Π̈ = R) = 1`, then
non-minimally-modifying actions are never strictly preferred by UDT:
`m(Π*(ȯ_ö,ö) = a_ö) > min_{a'} m(Π*(ȯ_ö,ö) = a') ⟹ E(U ∣ Π*(ȯ_ö,ö) = a_ö) ≤ max_{a'} E(U ∣ Π*(ȯ_ö,ö) = a')`."
Reading: literal. The conclusion's `max` ranges over `a' = a_ö`, so it holds for every attained
`a_ö` by `Finset.le_sup'` alone: **none of the binders `hDD`, `hCA`, `h1`, `hmod` is used.**
Severity: local error in the statement of the paper's main theorem. Surviving neighbour:
`selfTrust_repaired` (what the printed proof establishes).
Source: [[communication-trust-translated]] lines 472–478; original lines 480–486 (udt-rep-020, 2-008(b))
Kind: T
Fidelity: exact (the printed display)
Hyps: none used -/
theorem selfTrust_printed (_hDD : S.DecisionDetermined) (_hCA : S.HasCA)
    (_h1 : mass S.μ.w S.evFollowsR = 1) (o : OI) (e : OE) (a : AI × AE)
    (ha : (S.evS o e a).Nonempty)
    (_hmod : S.modS o e a > (S.attained o e).inf' ⟨a, by simpa using ha⟩ (S.modS o e)) :
    S.score o e a ≤ (S.attained o e).sup' ⟨a, by simpa using ha⟩ (S.score o e) :=
  Finset.le_sup' (S.score o e) (by simpa using ha)

/-- **Self-Trust, repaired (T11(b))**: under DD, `Π* ⊑ D_{I,B}`, `R ⊑ D_{I,B}`, communicative
alternatives and `P(Π̈ = R) = 1`, at every input `(ȯ, ö)` the UDT argmax contains a minimally
modifying action — a UDT agent never *strictly* prefers a modifying action. This is what the
printed proof establishes (translation lines 479–484): an argmax `a*` is attained; if it is not
minimally modifying, its communicative alternative `c` is, and scores the same by
`commExp_printed`, hence is an argmax too. The prose gloss "non-minimally-modifying actions are
never strictly preferred" is this statement, not the printed display.
Source: [[communication-trust-translated]] lines 479–484 (udt-rep-021); original lines 488–494
Kind: P
Fidelity: exact to the proof; stronger than the printed display (which is `T`)
Hyps: (a) throughout: DD, CA, `P(Π̈ = R) = 1` are the theorem's conditions; `Π* ⊑ D_{I,B}` and `R ⊑ D_{I,B}` are the proof's silent hypotheses; §3 (c) -/
theorem selfTrust_repaired (hDD : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    (hR : IsSubvariable S.DIB S.R) (hCA : S.HasCA) (h1 : mass S.μ.w S.evFollowsR = 1)
    (o : OI) (e : OE) : ∃ a, S.MinMod o e a ∧ IsArgmax (S.score o e) a := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (univ : Finset (AI × AE)) (S.score o e)
    ⟨S.polS S.w₀ (o, e), Finset.mem_univ _⟩
  have hArg : IsArgmax (S.score o e) a := fun a' => hmax a' (Finset.mem_univ _)
  have ha : (S.evS o e a).Nonempty := S.evS_nonempty_of_isArgmax hArg
  by_cases hmm : S.MinMod o e a
  · exact ⟨a, hmm, hArg⟩
  · obtain ⟨c, hc⟩ := hCA o e a ha
    refine ⟨c, hc.1, fun a' => ?_⟩
    rw [← S.commExp_printed hDD hsub hR h1 hc ha]
    exact hArg a'

open Classical in
/-- **The sup over minimally modifying actions is the sup over all actions** (T11(b), the
equivalent form of udt-rep-021).
Source: udt-rep-021 (the `max_{a' minimally modifying} = max_{a'}` form)
Kind: C
Fidelity: exact
Hyps: as `selfTrust_repaired`; §3 (c) -/
theorem selfTrust_sup_eq (hDD : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    (hR : IsSubvariable S.DIB S.R) (hCA : S.HasCA) (h1 : mass S.μ.w S.evFollowsR = 1)
    (o : OI) (e : OE) :
    ∃ hne : (univ.filter fun a => S.MinMod o e a).Nonempty,
      (univ.filter fun a => S.MinMod o e a).sup' hne (S.score o e) =
        univ.sup' ⟨S.polS S.w₀ (o, e), Finset.mem_univ _⟩ (S.score o e) := by
  obtain ⟨a, hmm, hArg⟩ := S.selfTrust_repaired hDD hsub hR hCA h1 o e
  refine ⟨⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hmm⟩⟩, le_antisymm ?_ ?_⟩
  · exact Finset.sup'_mono _ (Finset.filter_subset _ _) _
  · rw [Finset.sup'_le_iff]
    intro b _
    exact (hArg b).trans (Finset.le_sup' (S.score o e) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmm⟩))

/-! ### T17(ii): the strict-argmax ceiling -/

/-- **A unique UDT argmax is minimally modifying** (T17(ii)): under the hypotheses of the repaired
Self-Trust theorem, if the score at `(ȯ, ö)` has a strict argmax, it is minimally modifying. One
line from `selfTrust_repaired`; this is the only "strict" version available without a tie-break —
`Witness.lean` shows a tie between a modifying and a non-modifying action under all the
hypotheses.
Source: mandate T17(ii)
Kind: C
Fidelity: n/a (extension)
Hyps: as `selfTrust_repaired` plus `IsStrictArgmax`; §3 (c) -/
theorem minMod_of_isStrictArgmax (hDD : S.DecisionDetermined) (hsub : IsSubvariable S.DIB S.polS)
    (hR : IsSubvariable S.DIB S.R) (hCA : S.HasCA) (h1 : mass S.μ.w S.evFollowsR = 1)
    {o : OI} {e : OE} {a : AI × AE} (hstrict : IsStrictArgmax (S.score o e) a) :
    S.MinMod o e a := by
  obtain ⟨a', hmm, hArg⟩ := S.selfTrust_repaired hDD hsub hR hCA h1 o e
  by_cases h : a' = a
  · exact h ▸ hmm
  · exact absurd (hArg a) (not_le.2 (hstrict a' h))

/-- **Under DD no strict preference can come from a modification cost (T17(i))**: if `U` is a
function of `E` and some modified world shares its environment with an unmodified one, then `U`
cannot be strictly lower on every modified world than on every unmodified world with the same `E`.
Modification is internal (`P ⊑ Ȯ`), so it is invisible to `E` unless the structure makes it visible.
Source: mandate T17(i)
Kind: L
Fidelity: n/a (a finding)
Hyps: none -/
theorem no_modification_cost (hDD : S.DecisionDetermined) {ω ω' : Ω} (hω : S.IsModified ω)
    (hω' : ¬ S.IsModified ω') (hE : S.E ω = S.E ω') :
    ¬ (∀ ω₁ ω₂, S.IsModified ω₁ → ¬ S.IsModified ω₂ → S.E ω₁ = S.E ω₂ → S.U ω₁ < S.U ω₂) := by
  intro h
  exact lt_irrefl _ ((h ω ω' hω hω' hE).trans_eq (hDD.1 ω ω' hE).symm)

end ConcreteDS

end Cleanroom.Udt.UdtCommTrust
