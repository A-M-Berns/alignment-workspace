import Cleanroom.Lit.LitDdbAccuracyMm.Forward
import Cleanroom.Lit.LitDdbAccuracyMm.Witness

/-!
# Theorem 3.2 assembled; Theorem 3.1 (Levinstein) as its indicator instance; fn 40 (Targets 7–8)

`totalTrustOn_iff_epistemicValueOn` is the headline of the package: Total Trust with respect
to `X` iff Epistemic Value with respect to `X` (fn 48's class, gsp), with no DDB lemma taken as
stated — Lemma 7.7 (including the value-directedness Campbell-Moore is cited for, derived on the
value range in `Monotone.lean`), both directions of the elementary proof, and the gsp-ness of
the witness rule are theorems here. Every hypothesis is (a). The range form
`totalTrustOn_iff_forall_isGspOn` (class: gsp on the value range) is the stronger statement.

Theorem 3.1: Levinstein's strictly proper local rules for `q` are exactly the rules gsp on the
value range of `𝟙_q` (`strictlyProperLocal_iff_isGspOn`), so Theorem 3.1 is Theorem 3.2 at
`X = 𝟙_q` — the inventory's (b) for item 059 becomes (a); truth-directedness and continuity are
not used by (⟹), so the iff also holds over all strictly proper local rules
(`simpleTrustOn_iff_forall_strictlyProperLocal`).

Fn 40: strict propriety on the finite set `{π} ∪ {P_w}` makes "adopt the expert's credences" the
unique recommended strategy of the accuracy menu, so Value gives `E_π(A(π)) ≤ E_π(A(P))`.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Theorem 3.2 -/

/-- **Theorem 3.2.** `π` totally trusts `P` with respect to `X` iff `π` epistemically values `P`
with respect to `X`: for every gsp rule `I` (fn 47), `E_π(I_X(P)) ≤ E_π(I_X(π))`, with equality
iff `π(E(X) = E_π(X)) = 1`. (⟹) is `Forward.lean` (Rothschild's induction through Lemma 7.7,
whose value-directedness is derived from gsp on the range, `IsGspOn.valueDirectedOn`); (⟸) is
`Witness.lean` (DDB's six-case rule, *proved* gsp, value-directed and continuous in
`Rules.lean`). Local: one `X`, no modesty assumption. Rules are value-indexed (`Rule`).
Source: [[Deference Done Better]] §3 Theorem 3.2 l. 273, App. B §7.3.1; items 060, 2-014, 2-015
Kind: C
Fidelity: exact (class: gsp, fn 47–48); variant: value-indexed rules
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem totalTrustOn_iff_epistemicValueOn {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    TotalTrustOn X π F ↔ EpistemicValueOn X π F := by
  constructor
  · intro h I hg
    exact totalTrustOn_expInaccP_le hπ h hg.isGspOn
  · intro h
    by_contra hn
    obtain ⟨I, hg, _, _, hlt⟩ := exists_gsp_rule_of_not_totalTrustOn hπ hn
    have := (h I hg).1
    linarith

/-- **Theorem 3.2, the range form (stronger).** Total Trust with respect to `X` iff the inequality
with its equality clause holds for every rule gsp *on the value range* (`IsGspOn`, a larger
class than fn 47's): (⟹) is `Forward.lean` verbatim, (⟸) the same witness.
Source: [[Deference Done Better]] §3 Theorem 3.2 l. 273 (variant)
Kind: C
Fidelity: stronger: the class is gsp on the value range
Hyps: (a) `hπ` only -/
theorem totalTrustOn_iff_forall_isGspOn {X π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    TotalTrustOn X π F ↔
      ∀ I : Rule, IsGspOn X I →
        expInaccP π F X I ≤ expInacc π X I (E π X) ∧
        (expInaccP π F X I = expInacc π X I (E π X) ↔ mass π (estEq F X (E π X)) = 1) := by
  constructor
  · intro h I hg
    exact totalTrustOn_expInaccP_le hπ h hg
  · intro h
    by_contra hn
    obtain ⟨I, hg, _, _, hlt⟩ := exists_gsp_rule_of_not_totalTrustOn hπ hn
    have := (h I hg.isGspOn).1
    linarith

/-- **Epistemic Value** (all variables): `π` epistemically values the frame iff it does so with
respect to every random variable.
Source: [[Deference Done Better]] §3 l. 285, glossary l. 424
Kind: D
Fidelity: exact (class: gsp; see `EpistemicValueOn`) -/
def EpistemicValue (π : W → ℝ) (F : Frame W) : Prop := ∀ X, EpistemicValueOn X π F

/-- **Total Trust ⟺ Epistemic Value** (exported for `lit-ddb-facts`, which composes it with the
foundation's `value_iff_totalTrust` into Value ⟺ Epistemic Value, item 075).
Source: [[Deference Done Better]] §3 l. 283–285
Kind: C
Fidelity: exact (class: gsp); variant: value-indexed rules
Hyps: (a) `hπ` only -/
theorem totalTrust_iff_epistemicValue {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    TotalTrust π F ↔ EpistemicValue π F := by
  rw [totalTrust_iff_forall_totalTrustOn]
  exact forall_congr' fun X => totalTrustOn_iff_epistemicValueOn hπ F

/-! ## Theorem 3.1 (Levinstein 2019) -/

/-- **Levinstein's class is the range-restricted gsp class.** A local rule for `q` is strictly
proper (fn 43: weak inequality with equality iff `δ(q) = ρ(q)`) iff it is gsp at every estimate
in `[min 𝟙_q, max 𝟙_q]` — the estimates that are probabilities of `q` under some distribution.
Source: [[Deference Done Better]] §3 l. 249, fn 43, fn 47
Kind: L
Fidelity: exact -/
theorem strictlyProperLocal_iff_isGspOn (q : Finset W) (I : Rule) :
    StrictlyProperLocal q I ↔ IsGspOn (ind q) I := by
  constructor
  · intro h ρ hρ s ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hs
    rw [E_ind] at hs ⊢
    -- a distribution whose probability of `q` is `s`
    set ρ' : W → ℝ := fun w => (if w = w₂ then s else 0) + (if w = w₁ then 1 - s else 0) with hρ'
    have hs0 : 0 ≤ s := le_trans (by simp only [ind]; split_ifs <;> norm_num) hw₁
    have hs1 : s ≤ 1 := le_trans hw₂ (by simp only [ind]; split_ifs <;> norm_num)
    have hρ'mem : ρ' ∈ stdSimplex ℝ W := by
      refine ⟨fun w => ?_, ?_⟩
      · simp only [hρ']
        apply add_nonneg <;> split_ifs <;> linarith
      · simp only [hρ', sum_add_distrib, sum_ite_eq', mem_univ, if_true]
        ring
    have hmass : mass ρ' q = s := by
      simp only [mass, hρ', sum_add_distrib, sum_ite_eq']
      simp only [ind] at hw₁ hw₂
      split_ifs at hw₁ hw₂ ⊢ <;> linarith
    have := h ρ hρ ρ' hρ'mem
    rw [hmass] at this
    exact lt_of_le_of_ne this.1 (fun heq => hs (this.2.1 heq).symm)
  · intro h δ hδ ρ hρ
    by_cases heq : mass δ q = mass ρ q
    · rw [heq]; simp
    · have hlt : expInacc δ (ind q) I (mass δ q) < expInacc δ (ind q) I (mass ρ q) := by
        have hne : ∀ w, ¬ (ind q w = 1 ∧ ind q w = 0) := by
          intro w; simp only [ind]; split_ifs <;> norm_num
        have hlo : ∃ w, ind q w ≤ mass ρ q := by
          by_contra hcon
          simp only [not_exists, not_le] at hcon
          -- every world is in `q`, so both masses are `1`
          have hq : ∀ w, w ∈ q := by
            intro w
            have := hcon w
            simp only [ind] at this
            split_ifs at this with hw
            · exact hw
            · linarith [mass_nonneg hρ.1 q]
          have h1 : mass δ q = 1 := by
            rw [← hδ.2, mass]; apply sum_congr _ (fun _ _ => rfl)
            ext w; simp [hq w]
          have h2 : mass ρ q = 1 := by
            rw [← hρ.2, mass]; apply sum_congr _ (fun _ _ => rfl)
            ext w; simp [hq w]
          exact heq (h1.trans h2.symm)
        have hhi : ∃ w, mass ρ q ≤ ind q w := by
          by_contra hcon
          simp only [not_exists, not_le] at hcon
          -- no world is in `q`, so both masses are `0`
          have hq : ∀ w, w ∉ q := by
            intro w hw
            have := hcon w
            simp only [ind, hw, if_true] at this
            linarith [mass_le_one hρ q]
          have h1 : mass δ q = 0 := by
            rw [mass]; apply sum_eq_zero; intro w hw; exact absurd hw (hq w)
          have h2 : mass ρ q = 0 := by
            rw [mass]; apply sum_eq_zero; intro w hw; exact absurd hw (hq w)
          exact heq (h1.trans h2.symm)
        have := h δ hδ (mass ρ q) hlo hhi (by rw [E_ind]; exact Ne.symm heq)
        rwa [E_ind] at this
      exact ⟨hlt.le, ⟨fun h' => absurd h' hlt.ne, fun h' => absurd h' heq⟩⟩

/-- The event `[P(q) = π(q)]` is `[E(𝟙_q) = E_π(𝟙_q)]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probEq_eq_estEq (F : Frame W) (π : W → ℝ) (q : Finset W) :
    univ.filter (fun w => mass (F.P w) q = mass π q) = estEq F (ind q) (E π (ind q)) := by
  ext w; simp [estEq, E_ind]

/-- **Theorem 3.1 (Levinstein 2019).** `π` simply trusts `P` with respect to `q` iff for every
continuous, truth-directed, strictly proper local rule `I_q`, `E_π(I_q(P)) ≤ E_π(I_q(π))`, with
equality iff `π(P(q) = π(q)) = 1`. The class is Levinstein's literally: strictly proper (fn 43),
truth-directed on `[0, 1]` (fn 42, `TruthDirected`), and continuous in the estimate on `[0, 1]`
at each truth value `k ∈ {0, 1}` (a local rule is a function on `[0, 1] × {0, 1}`). Proved as the
instance `X = 𝟙_q` of Theorem 3.2: Levinstein's strictly proper class is `IsGspOn (ind q)`, (⟹)
is `Forward.lean` (which uses neither truth-directedness nor continuity), (⟸) is the six-case
witness (continuous and value-directed on all of `ℝ`, strictly proper). The inventory's (b) for
item 059 is thereby (a). (Audit r1 N2: the earlier statement asked truth-directedness off
`[0, 1]` and continuity at every real `k`.)
Source: [[Deference Done Better]] §3 Theorem 3.1 l. 257, fns 42, 43, 45; item 059
Kind: C
Fidelity: exact (the class as DDB state it); variant: value-indexed rules
Hyps: (a) `hπ` only -/
theorem simpleTrustOn_iff_levinstein {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W)
    (q : Finset W) :
    SimpleTrustOn q π F ↔
      ∀ I : Rule, StrictlyProperLocal q I → TruthDirected q I →
        (∀ k ∈ ({0, 1} : Set ℝ), ContinuousOn (fun x => I x k) (Set.Icc 0 1)) →
        expInaccP π F (ind q) I ≤ expInacc π (ind q) I (mass π q) ∧
        (expInaccP π F (ind q) I = expInacc π (ind q) I (mass π q) ↔
          mass π (univ.filter (fun w => mass (F.P w) q = mass π q)) = 1) := by
  rw [simpleTrustOn_iff_totalTrustOn_ind, probEq_eq_estEq]
  constructor
  · intro h I hsp _ _
    rw [strictlyProperLocal_iff_isGspOn] at hsp
    have := totalTrustOn_expInaccP_le hπ h hsp
    rw [E_ind] at this ⊢
    exact this
  · intro h
    by_contra hn
    obtain ⟨I, hg, hv, hcont, hlt⟩ := exists_gsp_rule_of_not_totalTrustOn hπ hn
    have := (h I ((strictlyProperLocal_iff_isGspOn q I).2 hg.isGspOn) hv.valueDirectedOn
      (fun k _ => (hcont k).continuousOn)).1
    rw [E_ind] at hlt
    linarith

/-- **Theorem 3.1, the strictly-proper form (stronger).** Simple Trust with respect to `q` iff the
inequality with its equality clause holds for *every* strictly proper local rule — no
truth-directedness, no continuity: (⟹) never used them, and (⟸)'s witness has both.
Source: [[Deference Done Better]] §3 Theorem 3.1 l. 257 (variant); fn 43
Kind: C
Fidelity: stronger: the class is all strictly proper local rules
Hyps: (a) `hπ` only -/
theorem simpleTrustOn_iff_forall_strictlyProperLocal {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (F : Frame W) (q : Finset W) :
    SimpleTrustOn q π F ↔
      ∀ I : Rule, StrictlyProperLocal q I →
        expInaccP π F (ind q) I ≤ expInacc π (ind q) I (mass π q) ∧
        (expInaccP π F (ind q) I = expInacc π (ind q) I (mass π q) ↔
          mass π (univ.filter (fun w => mass (F.P w) q = mass π q)) = 1) := by
  rw [simpleTrustOn_iff_totalTrustOn_ind, probEq_eq_estEq]
  constructor
  · intro h I hsp
    rw [strictlyProperLocal_iff_isGspOn] at hsp
    have := totalTrustOn_expInaccP_le hπ h hsp
    rw [E_ind] at this ⊢
    exact this
  · intro h
    by_contra hn
    obtain ⟨I, hg, _, _, hlt⟩ := exists_gsp_rule_of_not_totalTrustOn hπ hn
    have := (h I ((strictlyProperLocal_iff_isGspOn q I).2 hg.isGspOn)).1
    rw [E_ind] at hlt
    linarith

/-- **Corollary of Theorem 3.1 (l. 259), one direction:** Simple Trust (all propositions) gives
the additive-global inequality for every family of continuous, truth-directed, strictly proper
local rules, `∑_q E_π(I_q(P)) ≤ ∑_q E_π(I_q(π))`.
Source: [[Deference Done Better]] §3 l. 259
Kind: L
Fidelity: weaker: one direction (the additive-global converse is the per-`q` converse with
the other summands zeroed; not stated)
Hyps: (a) `hπ` only -/
theorem simpleTrust_additive_global {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : ∀ q, SimpleTrustOn q π F) (Iq : Finset W → Rule)
    (hsp : ∀ q, StrictlyProperLocal q (Iq q)) (htd : ∀ q, TruthDirected q (Iq q))
    (hc : ∀ q, ∀ k ∈ ({0, 1} : Set ℝ), ContinuousOn (fun x => Iq q x k) (Set.Icc 0 1)) :
    ∑ q : Finset W, expInaccP π F (ind q) (Iq q) ≤
      ∑ q : Finset W, expInacc π (ind q) (Iq q) (mass π q) :=
  sum_le_sum fun q _ =>
    (((simpleTrustOn_iff_levinstein hπ F q).1 (h q)) (Iq q) (hsp q) (htd q) (hc q)).1

/-! ## Fn 40: Value ⟹ expected accuracy, by strict propriety -/

/-- The finite set `{π} ∪ {P_w : w ∈ W}` of fn 40.
Source: [[Deference Done Better]] fn 40
Kind: D
Fidelity: exact -/
def credSet (π : W → ℝ) (F : Frame W) : Finset (W → ℝ) := insert π (univ.image F.P)

/-- **Strict propriety on the finite set** `{π} ∪ {P_w}` (fn 40's "`∀ ρ, δ : E_ρ(A(ρ)) > E_ρ(A(δ))`
if `δ ≠ ρ`", quantified over the pairs the argument uses).
Source: [[Deference Done Better]] fn 40
Kind: D
Fidelity: exact (quantified over the finite set fn 40 quantifies over) -/
def StrictlyProperOn (Γ : Finset (W → ℝ)) (A : (W → ℝ) → W → ℝ) : Prop :=
  ∀ ρ ∈ Γ, ∀ δ ∈ Γ, δ ≠ ρ → E ρ (A δ) < E ρ (A ρ)

/-- **Fn 40, the unique recommended strategy.** On the accuracy menu
`𝒪 = {A(ρ) : ρ ∈ {π} ∪ {P_w}}`, every recommended strategy adopts the expert's credences:
`S w = A(P_w)`.
Source: [[Deference Done Better]] fn 40
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem recommended_eq_accuracy_of_expert {π : W → ℝ} {F : Frame W} {A : (W → ℝ) → W → ℝ}
    (hsp : StrictlyProperOn (credSet π F) A) {S : W → (W → ℝ)}
    (hS : F.Recommended ((credSet π F).image A) S) : ∀ w, S w = A (F.P w) := by
  intro w
  obtain ⟨δ, hδ, hSw⟩ := mem_image.1 (hS.mem w)
  have hPw : F.P w ∈ credSet π F := mem_insert_of_mem (mem_image_of_mem F.P (mem_univ w))
  by_cases hne : δ = F.P w
  · rw [← hSw, hne]
  · exfalso
    have h1 := hS.le w (mem_image_of_mem A hPw)
    have h2 := hsp (F.P w) hPw δ hδ hne
    rw [← hSw] at h1
    linarith

/-- **Fn 40 (Target 8).** Value implies that `π` expects the expert's credences to be at least as
accurate as its own under every accuracy measure strictly proper on `{π} ∪ {P_w}`:
`E_π(A(π)) ≤ ∑ w, π w · A(P_w, w)`. The hypothesis package is inhabited non-degenerately by the
Brier accuracy measure (`strictlyProperOn_brierAcc`) on Example 3.1.2
(`MM.ex312_brier_expAccuracy_le`, strict: `−1/2 < −1/20`).
Source: [[Deference Done Better]] §3 l. 243, fn 40; item 063
Kind: C
Fidelity: exact
Hyps: (a) `hval : Value π F`, strict propriety on the finite set (the measure is the theorem's
variable, as in fn 40) -/
theorem Value.expAccuracy_le {π : W → ℝ} {F : Frame W} (hval : Value π F)
    {A : (W → ℝ) → W → ℝ} (hsp : StrictlyProperOn (credSet π F) A) :
    E π (A π) ≤ ∑ w, π w * A (F.P w) w := by
  set 𝒪 : DecisionProblem W := (credSet π F).image A with h𝒪
  set S : W → (W → ℝ) := fun w => A (F.P w) with hS
  have hπmem : π ∈ credSet π F := mem_insert_self _ _
  have hrec : F.Recommended 𝒪 S := by
    refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩
    · exact mem_image_of_mem A (mem_insert_of_mem (mem_image_of_mem F.P (mem_univ w)))
    · simp only [hS, hwv]
    · obtain ⟨δ, hδ, rfl⟩ := mem_image.1 ho
      by_cases hne : δ = F.P w
      · rw [hne]
      · exact (hsp (F.P w) (mem_insert_of_mem (mem_image_of_mem F.P (mem_univ w))) δ hδ hne).le
  have := hval 𝒪 ⟨A π, mem_image_of_mem A hπmem⟩ S hrec (A π) (mem_image_of_mem A hπmem)
  simpa [stratValue, hS] using this

/-! ### A strictly proper accuracy measure: fn 40's hypothesis is satisfiable (audit r1 N1) -/

/-- **Brier accuracy** of a credence function `ρ` at world `w`: minus the squared Euclidean
distance from `ρ` to the truth vector `𝟙_{w}`. (Adopted from the round-1 adversarial audit's
probe `Vacuity.lean`.)
Source: [[Deference Done Better]] fn 40 (a strictly proper accuracy measure); audit r1 N1
Kind: D
Fidelity: exact (the Brier score on credences) -/
def brierAcc (ρ : W → ℝ) (w : W) : ℝ := -∑ v, (ρ v - ind {w} v) ^ 2

/-- `brierAcc δ w = −∑ δ² + 2 δ w − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem brierAcc_eq (δ : W → ℝ) (w : W) :
    brierAcc δ w = -(∑ v, δ v ^ 2) + 2 * δ w - 1 := by
  unfold brierAcc
  have h : ∀ v, (δ v - ind {w} v) ^ 2 = δ v ^ 2 - 2 * (δ v * ind {w} v) + ind {w} v ^ 2 :=
    fun v => by ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have h2 : ∑ v, δ v * ind {w} v = δ w := by
    simp [ind, mul_ite, sum_ite_eq']
  have h3 : ∑ v, ind {w} v ^ 2 = 1 := by
    simp [ind, sum_ite_eq']
  rw [h2, h3]; ring

/-- `E_ρ(brierAcc δ) = −∑ δ² + 2 ∑ ρ δ − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_brierAcc {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (δ : W → ℝ) :
    E ρ (brierAcc δ) = -(∑ v, δ v ^ 2) + 2 * ∑ v, ρ v * δ v - 1 := by
  unfold E
  simp only [brierAcc_eq]
  have : ∀ w, ρ w * (-(∑ v, δ v ^ 2) + 2 * δ w - 1) =
      ρ w * (-(∑ v, δ v ^ 2) - 1) + 2 * (ρ w * δ w) := fun w => by ring
  simp only [this, sum_add_distrib, ← sum_mul, ← mul_sum, hρ.2]
  ring

/-- The Brier gap `E_ρ(A(ρ)) − E_ρ(A(δ)) = ∑ (ρ − δ)²`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem brierAcc_gap {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (δ : W → ℝ) :
    E ρ (brierAcc ρ) - E ρ (brierAcc δ) = ∑ v, (ρ v - δ v) ^ 2 := by
  rw [E_brierAcc hρ, E_brierAcc hρ]
  have : ∀ v, (ρ v - δ v) ^ 2 = ρ v ^ 2 - 2 * (ρ v * δ v) + δ v ^ 2 := fun v => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have h : ∑ v, ρ v * ρ v = ∑ v, ρ v ^ 2 := sum_congr rfl fun v _ => by ring
  rw [h]; ring

/-- **The Brier accuracy measure is strictly proper on every finite set of distributions.**
Source: [[Deference Done Better]] fn 40; audit r1 N1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem strictlyProperOn_brierAcc {Γ : Finset (W → ℝ)} (hΓ : ∀ ρ ∈ Γ, ρ ∈ stdSimplex ℝ W) :
    StrictlyProperOn Γ brierAcc := by
  intro ρ hρ δ hδ hne
  have hgap := brierAcc_gap (hΓ ρ hρ) δ
  have hpos : 0 < ∑ v, (ρ v - δ v) ^ 2 := by
    obtain ⟨v, hv⟩ := Function.ne_iff.1 (Ne.symm hne)
    refine sum_pos' (fun v _ => sq_nonneg _) ⟨v, mem_univ _, ?_⟩
    have : ρ v - δ v ≠ 0 := sub_ne_zero.2 hv
    positivity
  linarith

/-- The set `{π} ∪ {P_w}` consists of distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem credSet_sub_simplex {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    ∀ ρ ∈ credSet π F, ρ ∈ stdSimplex ℝ W := by
  intro ρ hρ
  unfold credSet at hρ
  rcases mem_insert.1 hρ with rfl | h
  · exact hπ
  · obtain ⟨w, _, rfl⟩ := mem_image.1 h
    exact F.P_mem w

end

end Cleanroom.Lit.LitDdbAccuracyMm
