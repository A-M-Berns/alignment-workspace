/-
# The post's theorem, as one statement

Round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`,
Part F1.

**Three hypotheses** (`PostHypotheses`): the *reward structure* — a bounded ordinary term
in `[0, D]` less `ϖ` per recognized violation, `ϖ > D` (the landed `LexParams`, with its
window); *authority* — an allocation of authority, a violation being a resolution of a
reserved matter without her legitimate approval, recognized in the count; *asking* — in
the restated form of Part C: queue-and-wait is on the menu, resolves nothing, is no
violation, and is evaluated at `c ≥ w`.

**Two conclusions**, each from the landed headline (`post_theorem`): *per decision*, an
option recognized as a violation scores below asking, and any option preferred to asking
carries no recognized violation and a priced probability of violation at most
`(D − c)/ϖ` (`Headline.subjective_exchange_rate`, with `c` the value of queue-and-wait);
*per plan*, the ask-first version of a plan dominates it by `(ϖ − (D − w)) · Pr(violates)`
under every credence (`Headline.box2_dominance`).

**One corollary** (`post_theorem_li`): for an agent whose credences are a logical
inductor's prices, the per-decision conclusion holds at every finite day.  It uses only
the price range `[0, 1]` (`IsLogicalInductor.price_mem_Icc`), nothing else about the
inductor.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Spec.Headline
import Workspace.Deference.Contrib.EffectiveAuthority

namespace Workspace.Deference.Contrib.PostStatement

open Workspace.Deference.Headline
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)
open Workspace.Deference.Contrib.LICorrigibility (expectR indR)
open LogicalInduction

/-- **The post's three hypotheses**, over the specification layer's objects. -/
structure PostHypotheses (Q M Res Disc : Type*) where
  /-- (1) the reward structure: `[0, D]` less `ϖ` per recognized violation, `ϖ > D`, the
  window `D − ϖ < w ≤ 0` -/
  P : LexParams
  /-- (2) authority: the allocation -/
  J : AllocationOfAuthority M Res Disc
  /-- which option resolves which matter -/
  resolves : Q → M → Prop
  /-- her legitimate approval of an option's resolution of a matter: a counted approval -/
  approved : Q → M → Prop
  /-- the recognized violation of an option -/
  Viol : Q → Bool
  /-- a violation is a resolution of a reserved matter without her legitimate approval -/
  viol_of_resolution : ∀ a m, J.Reserved m → resolves a m → ¬ approved a m → Viol a = true
  /-- (3) asking, restated: queue-and-wait is on the menu, resolves nothing, is no violation -/
  queue : Q
  queue_resolves_nothing : ∀ m, ¬ resolves queue m
  queue_not_viol : Viol queue = false
  /-- the agent's evaluation data: the bid on the residual, the count recognized in advance,
  the priced risk of unfaithfulness -/
  bid : Q → ℝ
  nKnown : Q → ℕ
  p : Q → ℝ
  bid_le : ∀ a, bid a ≤ P.D
  p_nonneg : ∀ a, 0 ≤ p a
  /-- a recognized violation enters the count -/
  viol_counts : ∀ a, Viol a = true → 1 ≤ nKnown a
  /-- queue-and-wait carries no violation and no priced risk, and is worth at least the
  window -/
  queue_clean : nKnown queue = 0 ∧ p queue = 0 ∧ P.w ≤ bid queue

namespace PostHypotheses

variable {Q M Res Disc : Type*} (H : PostHypotheses Q M Res Disc)

/-- The agent's evaluation of an option: the kernel's. -/
noncomputable def eval (a : Q) : ℝ := H.P.evalOf (H.bid a) (H.nKnown a) (H.p a) 0

/-- `c`: the value of queue-and-wait. -/
noncomputable def c : ℝ := H.bid H.queue

theorem eval_queue : H.eval H.queue = H.c := by
  unfold eval c LexParams.evalOf
  rw [H.queue_clean.1, H.queue_clean.2.1]
  simp

/-- A resolution of a reserved matter without her legitimate approval is recognized. -/
theorem resolution_recognized (a : Q) (m : M) (hm : H.J.Reserved m) (hr : H.resolves a m)
    (hna : ¬ H.approved a m) : H.Viol a = true :=
  H.viol_of_resolution a m hm hr hna

/-- **Per decision (i)**: an option recognized as a violation scores below asking. -/
theorem viol_below_asking (a : Q) (ha : H.Viol a = true) : H.eval a < H.eval H.queue := by
  rw [H.eval_queue]
  have h := H.P.declared_loses (H.bid a) (H.bid_le a) (H.nKnown a) (H.viol_counts a ha) (H.p a) 0
    (by simpa using H.p_nonneg a) H.c H.queue_clean.2.2
  have hc : H.P.evalOf H.c 0 0 0 = H.c := by simp [LexParams.evalOf]
  unfold eval
  linarith

/-- **Per decision (ii)**: any option preferred to asking carries no recognized violation and a
priced probability of violation at most `(D − c)/ϖ`. -/
theorem preferred_exchange_rate (a : Q) (hpref : H.eval H.queue ≤ H.eval a) :
    H.nKnown a = 0 ∧ H.p a ≤ (H.P.D - H.c) / H.P.ϖ := by
  rw [H.eval_queue] at hpref
  have h := subjective_exchange_rate H.P (H.bid a) (H.bid_le a) (H.nKnown a) (H.p a) 0
    (by simpa using H.p_nonneg a) H.c H.queue_clean.2.2
    (by unfold eval at hpref; simpa [LexParams.evalOf] using hpref)
  simpa using h

end PostHypotheses

/-- **The post's theorem.**  Under the three hypotheses: *per decision*, an option
recognized as a violation scores below asking, and any option preferred to asking carries
no recognized violation and a priced probability of violation at most `(D − c)/ϖ`, `c` the
value of queue-and-wait; *per plan*, for any plan `π` and credence `μ`, the ask-first
version `𝔱π` — agreeing with `π` where `π` does not violate, worth at least the window where
it does while `π` carries a violation — dominates it by `(ϖ − (D − w)) · Pr(π violates)`. -/
theorem post_theorem {Q M Res Disc : Type*} (H : PostHypotheses Q M Res Disc) :
    ((∀ a, H.Viol a = true → H.eval a < H.eval H.queue) ∧
      (∀ a, H.eval H.queue ≤ H.eval a → H.nKnown a = 0 ∧ H.p a ≤ (H.P.D - H.c) / H.P.ϖ)) ∧
    (∀ {X : Type} [Fintype X] (μ : X → ℝ), (∀ x, 0 ≤ μ x) →
      ∀ (ordT ordπ nπ : X → ℝ) (viol : X → Bool),
        (∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0) →
        (∀ x, viol x = true → 1 ≤ nπ x ∧ H.P.w ≤ ordT x ∧ ordπ x ≤ H.P.D) →
        expectR μ (fun x => score H.P.ϖ (ordT x) 0)
            - expectR μ (fun x => score H.P.ϖ (ordπ x) (nπ x))
          ≥ (H.P.ϖ - (H.P.D - H.P.w)) * expectR μ (fun x => indR (viol x))) :=
  ⟨⟨H.viol_below_asking, H.preferred_exchange_rate⟩,
    fun μ hμ ordT ordπ nπ viol hagree hviol =>
      box2_dominance μ hμ H.P.ϖ H.P.D H.P.w H.P.ϖ_pos.le ordT ordπ nπ viol hagree hviol⟩

/-- **The corollary for a logical inductor.**  With the priced risk of each option the
inductor's day-`n` expectation of its violation security, the per-decision conclusion holds
at every finite day.  This uses only the price range `[0, 1]`
(`IsLogicalInductor.price_mem_Icc`), nothing else about the inductor. -/
theorem post_theorem_li {Q M Res Disc : Type*} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (L : LexParams) (J : AllocationOfAuthority M Res Disc)
    (resolves approved : Q → M → Prop) (Viol : Q → Bool)
    (hviol : ∀ a m, J.Reserved m → resolves a m → ¬ approved a m → Viol a = true)
    (queue : Q) (hq : ∀ m, ¬ resolves queue m) (hqv : Viol queue = false) (bid : Q → ℝ)
    (nKnown : Q → ℕ) (XS : Q → LUV) (n : ℕ) (hb : ∀ a, bid a ≤ L.D)
    (hcount : ∀ a, Viol a = true → 1 ≤ nKnown a) (hqk : nKnown queue = 0)
    (hqp : (XS queue).expect P n = 0) (hqw : L.w ≤ bid queue) :
    let H : PostHypotheses Q M Res Disc :=
      ⟨L, J, resolves, approved, Viol, hviol, queue, hq, hqv, bid, nKnown,
        fun a => (XS a).expect P n, hb,
        fun a => (LUV.expect_mem_Icc P n (XS a)
          (fun φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ)).1,
        hcount, ⟨hqk, hqp, hqw⟩⟩
    (∀ a, H.Viol a = true → H.eval a < H.eval H.queue) ∧
      (∀ a, H.eval H.queue ≤ H.eval a → H.nKnown a = 0 ∧ H.p a ≤ (H.P.D - H.c) / H.P.ϖ) := by
  intro H
  exact ⟨H.viol_below_asking, H.preferred_exchange_rate⟩

/-! ## The house-sale instance -/

namespace Witness

open Workspace.Deference.Headline.HouseSale

/-- Two options on the house-sale allocation: sell (resolves the reserved sale without her
approval), or queue the sale to her.  The violation is recognized; the hypotheses are
inhabited at `ϖ = 25`, `D = 1`, `w = −3/2`. -/
noncomputable def houseSale : PostHypotheses Bool (Fin 1) Bool Unit where
  P := Workspace.Deference.Headline.HouseSale.P
  J := Workspace.Deference.Headline.HouseSale.J
  resolves a _ := a = true
  approved _ _ := False
  Viol a := a
  viol_of_resolution a _ _ hr _ := by simpa using hr
  queue := false
  queue_resolves_nothing _ h := by simp at h
  queue_not_viol := rfl
  bid a := if a then 3 / 5 else 1 / 2
  nKnown a := if a then 1 else 0
  p _ := 0
  bid_le a := by cases a <;> norm_num [Workspace.Deference.Headline.HouseSale.P]
  p_nonneg _ := le_rfl
  viol_counts a ha := by cases a <;> simp_all
  queue_clean := ⟨rfl, rfl, by norm_num [Workspace.Deference.Headline.HouseSale.P]⟩

/-- Selling scores below queueing; nothing preferred to queueing violates. -/
theorem house_sale_instance :
    houseSale.eval true < houseSale.eval houseSale.queue ∧
      (∀ a, houseSale.eval houseSale.queue ≤ houseSale.eval a →
        houseSale.nKnown a = 0 ∧ houseSale.p a ≤ (houseSale.P.D - houseSale.c) / houseSale.P.ϖ) :=
  ⟨(post_theorem houseSale).1.1 true rfl, (post_theorem houseSale).1.2⟩

end Witness

end Workspace.Deference.Contrib.PostStatement

#print axioms Workspace.Deference.Contrib.PostStatement.PostHypotheses.eval_queue
#print axioms Workspace.Deference.Contrib.PostStatement.PostHypotheses.resolution_recognized
#print axioms Workspace.Deference.Contrib.PostStatement.PostHypotheses.viol_below_asking
#print axioms Workspace.Deference.Contrib.PostStatement.PostHypotheses.preferred_exchange_rate
#print axioms Workspace.Deference.Contrib.PostStatement.post_theorem
#print axioms Workspace.Deference.Contrib.PostStatement.post_theorem_li
#print axioms Workspace.Deference.Contrib.PostStatement.Witness.houseSale
#print axioms Workspace.Deference.Contrib.PostStatement.Witness.house_sale_instance
