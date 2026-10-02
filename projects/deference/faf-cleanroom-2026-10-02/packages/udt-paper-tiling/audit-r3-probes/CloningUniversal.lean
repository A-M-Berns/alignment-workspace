import Cleanroom.Udt.UdtPaperTiling.ThirdButtonPrior

/-!
Audit round 3, adversarial lens — probe for `naive_cloning_refuted` (T10(e), load-bearing 4)
and the claim, in the ledger row and F-9, that "the refutation is of 075's hypothesis and not of a
weaker one".

The notes state Communicative Cloning **for every** `a₁ ∈ 𝒜_o`
([[udt-tiling-working-notes-2025-06-30]] line 13, "Assumptions": "For every action `a₁ ∈ A_o`,
there is a communicative clone `cc(a₁)` which achieves the minimum modification probability while
achieving the same expected utility, provided communicated advice is followed"). The package's
`CommunicativeCloning Λ S o a₁ cc followed` is the instance at one `a₁`, and the refutation
establishes it at `a₁ = pill` only.

On the refutation model the universal form **fails**: at `a₁ = say10` the only positive point with
minimal modification probability is `say10` itself (`modProb say10 = 0 < 1 = modProb pill`), and
`chosenEU pre say10 = 5 ≠ 10 = 𝔼[U | π*(pre) = say10 ∧ followed]` — the package's own `numbers`.
So the model is not a countermodel to "CC (for every `a₁`) + PF ⟹ no strict preference for an
action of non-minimal modification probability": it violates that hypothesis. Worse for the
intended theorem's status, under the universal form the conclusion is a two-line consequence
whenever the clone of a minimal-modification action is itself (`cc_chain` below): CC at `a₁`
gives `𝔼[U | a₁] = 𝔼[U | cc ∧ F]`, CC at `cc` (clone `cc`) gives `𝔼[U | cc] = 𝔼[U | cc ∧ F]`, so
the two are equal. CC at a minimal action is "advice is followed, in value" in disguise, which is
exactly what the Third Button denies. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtPaperTiling.AuditR3Adv

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset CommClone

/-- **Under Communicative Cloning at `a₁` (clone `cc`) and at `cc` (clone `cc` itself), with the
same "followed" event, `a₁` and `cc` have the same chosen-point value** — the intended
conclusion of bli-paper-075 in two rewrites, with no fairness, faith-in-argmax or KDP step. -/
theorem cc_chain {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
    [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (Λ : PaperLayer P) (S : PaperStructure 𝒟 Act)
    (o : ↥𝒟) (a₁ cc : Act) (f : P.Ω → Prop) [DecidablePred f]
    (h₁ : CommunicativeCloning Λ S o a₁ cc f) (h₂ : CommunicativeCloning Λ S o cc cc f) :
    Λ.chosenEU o a₁ = Λ.chosenEU o cc := by
  rw [h₁.2.2, h₂.2.2]

/-- The positive points at `pre` are `pill = 3` and `say10 = 4`. -/
lemma point_cases {cc : Fin 5} (h : 0 < Λ.pointMass X1 cc) : cc = 3 ∨ cc = 4 := by
  unfold PaperLayer.pointMass at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [Λ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [chosen₀]
  | 1 => simp [chosen₀]
  | 2 => simp [chosen₀]

/-- **Communicative Cloning fails at `a₁ = say10` on the refutation model**, for every candidate
clone: `pill` is not of minimal modification probability (`1 > 0`), and `say10` as its own clone
would need `chosenEU pre say10 = 5` to equal `𝔼[U | say10 ∧ followed] = 10`. -/
theorem not_cc_say10 : ¬ ∃ cc, CommunicativeCloning Λ S X1 4 cc followed := by
  rintro ⟨cc, hpos, hmin, heq⟩
  obtain ⟨_, m4, _, v4, p3, p4, cf⟩ := numbers
  rcases point_cases hpos with rfl | rfl
  · have := hmin 4 (by simp [S]) (by rw [m4]; norm_num)
    rw [p3, p4] at this
    norm_num at this
  · rw [v4, cf] at heq
    norm_num at heq

/-- **The notes' universal Communicative Cloning does not hold on the refutation model**: so
`naive_cloning_refuted` refutes the single-instance form (CC at the pill) and not 075's
hypothesis as stated. -/
theorem cc_universal_fails :
    ¬ ∀ a₁ ∈ S.Aof X1, ∃ cc, CommunicativeCloning Λ S X1 a₁ cc followed := by
  intro h
  exact not_cc_say10 (h 4 (by simp [S]))

/-- **Had CC held at `say10` too (its clone is forced to be `say10`), the strict preference for
the pill would be impossible**: the two instances give `chosenEU pre pill = chosenEU pre say10`.
So on any model of the universal form with a self-cloning minimal action, the intended theorem
holds trivially; the Third Button is excluded by the hypothesis, not a counterexample to it. -/
theorem cc_at_say10_kills_refutation
    (h : CommunicativeCloning Λ S X1 4 4 followed) :
    Λ.chosenEU X1 3 = Λ.chosenEU X1 4 :=
  cc_chain Λ S X1 3 4 followed naive_cloning_refuted.1 h

end Cleanroom.Udt.UdtPaperTiling.AuditR3Adv
