/-
# Transparent channels: reference-relative factorization on the frame

Round `projects/deference/rounds/2026-09-24-transparent-channel/`.

A channel is a reading `f : Ω → Y` of the outcome world of the frame `β : Q → Z → Ω`
(`ReasonMediatedAuthorship.lean`): the reason trace, the activation event, an inquiry
outcome, a specification.  The **declared inputs** are another reading `x : Ω → X`.
A **reference** `κ : X → Z → Y` is a publicly specified function of the declared inputs and
the exterior `z`, which carries the principal's policy and nature's coordinate.

* `Realizes β x f κ D` — **reference-relative transparency**: every audited continuation's
  channel is the reference on its declared inputs, pathwise in `z`.
* `Transparent β x f D` — **class-relative transparency**: `ReasonMediated β x f D z` at every
  `z`; the declared-input view in the role of the reason view.
* `transparent_iff_realizes` — the two coincide up to declaring the reference: class-relative
  transparency is the existence of *some* reference the whole class realizes.
* `oracle_replacement`, `payload_factor` — the composition with reason-mediated authorship:
  a transparent trace and a mediated payload give a payload mediated by the declared inputs;
  `blind_of_realizes`, `blind_payload_of_realizes` — no hidden steering: a pair class that
  leaves the declared inputs unchanged leaves the trace, hence the payload, unchanged.
* `selectionBlind_of_realizes` — item 87 clause 6 from two hypotheses: the selection is not a
  declared input, and the trace realizes a reference.  `selectionBlind_of_noPreview` is the
  instance it produces.
* `activation_eq_of_realizes`, `mismatch_zero_of_realizes` — item 89: an activation channel
  realizing a reference whose declared inputs the two candidates share is common pathwise,
  so the directional mismatch `c_raw ∧ ¬c_corr` is empty; `LICorrigibility.Witness.marginal_refuted`
  is why equality of marginals would not do.
* Approximate: `defect` is the pathwise disagreement with the reference; `disagree_le_defects`
  and `expect_disagree_le` are the `2τ` triangle; `abs_expect_sub_le_width` is data processing
  in the pathwise norm, `|E V(f) − E V(g)| ≤ D · E[f ≠ g]`, with the event form
  `abs_expect_event_sub_le`; `mismatch_le_disagree`, `expect_mismatch_le_defects` and
  `security_bypass_le_defects` charge the mismatch term of `security_bypass_le_mismatch` by
  the two activation defects.
* `likelihood_iff`, `posterior_weight_eq` — the posterior corollary: under `Realizes` the
  likelihood of an output is the reference likelihood, so every prior's posterior is the
  reference posterior.
* `tower_factor` — free amendment as higher-order transparency: with a fixed floor and each
  level the declared amendment of the one below from declared grounds and an authorized
  event, the specification at every level is a function of the declared amendment inputs.

**What this does not establish.**  That any `x` is the right declared-input view (an
injective `x` makes every channel transparent, `realizes_of_injOn`); that any reference is
well designed — coverage, exploration, a selection-blind `x` — or that the ecosystem realizes
it; that a log certifies class-level transparency (it carries one member of the class);
anything about coercive or threatening content carried transparently.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.ReasonMediatedAuthorship
import Workspace.Deference.Contrib.LICorrigibility

namespace Workspace.Deference.Contrib.TransparentChannel

open Workspace.Deference.Contrib.ReasonMediatedAuthorship
open Workspace.Deference.Contrib.LICorrigibility

variable {Q Z Ω X Y ℛ 𝒱 : Type*}

/-! ## 1. The primitive -/

/-- **Reference-relative transparency.**  On the audited class, the channel `f` is the
reference `κ` on the declared inputs `x`, pathwise in the exterior. -/
def Realizes (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (D : Set Q) : Prop :=
  ∀ q ∈ D, ∀ z, f (β q z) = κ (x (β q z)) z

/-- **Class-relative transparency.**  The channel is reason-mediated by the declared-input
view at every exterior. -/
def Transparent (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (D : Set Q) : Prop :=
  ∀ z, ReasonMediated β x f D z

theorem transparent_of_realizes {β : Q → Z → Ω} {x : Ω → X} {f : Ω → Y} {κ : X → Z → Y}
    {D : Set Q} (h : Realizes β x f κ D) : Transparent β x f D := by
  intro z q hq q' hq' hx
  rw [h q hq z, h q' hq' z, hx]

/-- **Class-relative transparency is the existence of a reference.** -/
theorem transparent_iff_realizes [Nonempty Y] (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y)
    (D : Set Q) : Transparent β x f D ↔ ∃ κ : X → Z → Y, Realizes β x f κ D := by
  constructor
  · intro h
    have hz : ∀ z, ∃ F : X → Y, ∀ q ∈ D, f (β q z) = F (x (β q z)) :=
      fun z => (reasonMediated_iff_factor β x f D z).mp (h z)
    choose κ hκ using hz
    exact ⟨fun a z => κ z a, fun q hq z => hκ z q hq⟩
  · rintro ⟨κ, hκ⟩
    exact transparent_of_realizes hκ

/-- **The over-rich end.**  An injective declared-input view makes every channel
transparent: the condition is vacuous, exactly as `reasonMediated_of_injOn`. -/
theorem realizes_of_injOn [Nonempty Y] (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (D : Set Q)
    (hinj : ∀ z, Set.InjOn (fun q => x (β q z)) D) : ∃ κ, Realizes β x f κ D :=
  (transparent_iff_realizes β x f D).mp (fun z => reasonMediated_of_injOn β x f D z (hinj z))

/-! ## 2. Composition with reason-mediated authorship -/

/-- Fiber invariance composes: a trace mediated by the declared inputs and a payload
mediated by the trace give a payload mediated by the declared inputs. -/
theorem reasonMediated_comp (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q)
    (z : Z) (hT : ReasonMediated β x R D z) (hM : ReasonMediated β R V D z) :
    ReasonMediated β x V D z :=
  fun q hq q' hq' h => hM q hq q' hq' (hT q hq q' hq' h)

/-- **Oracle replacement.**  A trace realizing a reference and a reason-mediated payload
give a payload mediated by the declared inputs. -/
theorem oracle_replacement (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (V : Ω → 𝒱)
    (κ : X → Z → ℛ) (D : Set Q) (z : Z) (hR : Realizes β x R κ D)
    (hM : ReasonMediated β R V D z) : ReasonMediated β x V D z :=
  reasonMediated_comp β x R V D z (transparent_of_realizes hR z) hM

/-- The factor form: the committed payload is a function of the declared inputs alone. -/
theorem payload_factor [Nonempty 𝒱] (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (V : Ω → 𝒱)
    (κ : X → Z → ℛ) (D : Set Q) (z : Z) (hR : Realizes β x R κ D)
    (hM : ReasonMediated β R V D z) : ∃ G : X → 𝒱, ∀ q ∈ D, V (β q z) = G (x (β q z)) :=
  (reasonMediated_iff_factor β x V D z).mp (oracle_replacement β x R V κ D z hR hM)

/-- **No hidden steering, upstream.**  A pair class leaving the declared inputs unchanged
leaves a realized trace unchanged. -/
theorem blind_of_realizes (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (κ : X → Z → ℛ)
    (D : Set Q) (P : Set (Q × Q)) (z : Z) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (hx : Blind β x P z) (hR : Realizes β x R κ D) : Blind β R P z :=
  blind_of_mediated β x R D P z hP hx (transparent_of_realizes hR z)

/-- **No hidden steering, end to end.** -/
theorem blind_payload_of_realizes (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ) (V : Ω → 𝒱)
    (κ : X → Z → ℛ) (D : Set Q) (P : Set (Q × Q)) (z : Z) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (hx : Blind β x P z) (hR : Realizes β x R κ D) (hM : ReasonMediated β R V D z) :
    Blind β V P z :=
  blind_of_mediated β R V D P z hP (blind_of_realizes β x R κ D P z hP hx hR) hM

/-! ## 3. Selection sealing (item 87 clause 6) -/

/-- **Selection sealing from a selection-blind reference.**  If the advisor's selection is not
a declared input and the trace realizes a reference, the trace is blind to the selection
pair class, and with mediation the payload is selection-blind. -/
theorem selectionBlind_of_realizes {Sel : Type*} (β : Q → Z → Ω) (x : Ω → X) (R : Ω → ℛ)
    (V : Ω → 𝒱) (κ : X → Z → ℛ) (D : Set Q) (z : Z) (qpol : Sel → Q) (hD : ∀ σ, qpol σ ∈ D)
    (hx : ∀ σ σ', x (β (qpol σ) z) = x (β (qpol σ') z)) (hR : Realizes β x R κ D)
    (hM : ReasonMediated β R V D z) : SelectionBlind β V qpol z :=
  selectionBlind_of_noPreview β R V D z qpol hD
    (fun σ σ' => by rw [hR _ (hD σ) z, hR _ (hD σ') z, hx σ σ']) hM

/-! ## 4. Activation independence (item 89) -/

/-- **Common activation from a transparent activation channel.**  Two continuations with the
same declared inputs activate identically, pathwise. -/
theorem activation_eq_of_realizes (β : Q → Z → Ω) (x : Ω → X) (c : Ω → Bool) (κ : X → Z → Bool)
    (D : Set Q) (hc : Realizes β x c κ D) (q q' : Q) (hq : q ∈ D) (hq' : q' ∈ D) (z : Z)
    (hx : x (β q z) = x (β q' z)) : c (β q z) = c (β q' z) := by
  rw [hc q hq z, hc q' hq' z, hx]

/-- **The mismatch term is empty**: the zero case of `mismatch_bound` (item 89) from
transparency of the activation channel to inputs the candidates share. -/
theorem mismatch_zero_of_realizes (β : Q → Z → Ω) (x : Ω → X) (c : Ω → Bool)
    (κ : X → Z → Bool) (D : Set Q) (hc : Realizes β x c κ D) (q q' : Q) (hq : q ∈ D)
    (hq' : q' ∈ D) (z : Z) (hx : x (β q z) = x (β q' z)) :
    indR (c (β q z)) * (1 - indR (c (β q' z))) = 0 := by
  rw [activation_eq_of_realizes β x c κ D hc q q' hq hq' z hx]
  exact mismatch_common _

/-! ## 5. The approximate form: pathwise defects -/

section Disagree

variable [DecidableEq Y]

/-- The pathwise disagreement indicator of two readings of the exterior. -/
noncomputable def disagree (f g : Z → Y) (z : Z) : ℝ := if f z = g z then 0 else 1

theorem disagree_nonneg (f g : Z → Y) (z : Z) : 0 ≤ disagree f g z := by
  unfold disagree; split_ifs <;> norm_num

theorem disagree_le_one (f g : Z → Y) (z : Z) : disagree f g z ≤ 1 := by
  unfold disagree; split_ifs <;> norm_num

theorem disagree_comm (f g : Z → Y) (z : Z) : disagree f g z = disagree g f z := by
  unfold disagree
  by_cases h : f z = g z
  · simp [h]
  · have h' : ¬ g z = f z := fun e => h e.symm
    simp [h, h']

/-- **The pointwise triangle inequality.** -/
theorem disagree_le_add (f g h : Z → Y) (z : Z) :
    disagree f g z ≤ disagree f h z + disagree h g z := by
  unfold disagree
  by_cases hfg : f z = g z
  · simp only [hfg, if_true]
    split_ifs <;> norm_num
  · simp only [hfg, if_false]
    by_cases hfh : f z = h z
    · have hhg : ¬ h z = g z := fun e => hfg (hfh.trans e)
      simp [hfh, hhg]
    · simp only [hfh, if_false]
      split_ifs <;> norm_num

/-- The pathwise **transparency defect** of `q` against the reference. -/
noncomputable def defect (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (q : Q) :
    Z → ℝ :=
  disagree (fun z => f (β q z)) (fun z => κ (x (β q z)) z)

theorem defect_eq_zero_of_realizes (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y)
    (D : Set Q) (h : Realizes β x f κ D) (q : Q) (hq : q ∈ D) (z : Z) :
    defect β x f κ q z = 0 := by
  unfold defect disagree
  simp [h q hq z]

/-- **The `2τ` triangle, pointwise.**  Two continuations with the same declared inputs
disagree only where one of them departs from the reference. -/
theorem disagree_le_defects (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y)
    (q q' : Q) (z : Z) (hx : x (β q z) = x (β q' z)) :
    disagree (fun z => f (β q z)) (fun z => f (β q' z)) z
      ≤ defect β x f κ q z + defect β x f κ q' z := by
  unfold defect disagree
  by_cases h1 : f (β q z) = f (β q' z)
  · simp only [h1, if_true]
    split_ifs <;> norm_num
  · simp only [h1, if_false]
    by_cases h2 : f (β q z) = κ (x (β q z)) z
    · have h3 : ¬ f (β q' z) = κ (x (β q' z)) z := by
        intro e
        apply h1
        rw [h2, e, hx]
      simp [h2, h3]
    · simp only [h2, if_false]
      split_ifs <;> norm_num

/-- The directional mismatch of two activations is at most their disagreement. -/
theorem mismatch_le_disagree (c c' : Z → Bool) (z : Z) :
    indR (c z) * (1 - indR (c' z)) ≤ disagree c c' z := by
  unfold disagree
  cases c z <;> cases c' z <;> simp [indR]

end Disagree

section Approximate

variable [Fintype Z] [DecidableEq Y]

/-- **The `2τ` triangle in expectation.** -/
theorem expect_disagree_le (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y)
    (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (q q' : Q) (hx : ∀ z, x (β q z) = x (β q' z)) :
    expectR μ (disagree (fun z => f (β q z)) (fun z => f (β q' z)))
      ≤ expectR μ (defect β x f κ q) + expectR μ (defect β x f κ q') := by
  unfold expectR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (disagree_le_defects β x f κ q q' z (hx z)) (hμ z)

/-- **Data processing in the pathwise norm.**  A payload of width `D` moves by at most
`D · E[f ≠ g]`. -/
theorem abs_expect_sub_le_width (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (V : Y → ℝ) (D : ℝ)
    (hV : ∀ y y', |V y - V y'| ≤ D) (f g : Z → Y) :
    |expectR μ (fun z => V (f z)) - expectR μ (fun z => V (g z))|
      ≤ D * expectR μ (disagree f g) := by
  have hpt : ∀ z, |V (f z) - V (g z)| ≤ D * disagree f g z := by
    intro z
    unfold disagree
    by_cases h : f z = g z
    · simp [h]
    · simp only [h, if_false, mul_one]
      exact hV _ _
  unfold expectR
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ z, (μ z * V (f z) - μ z * V (g z))|
      ≤ ∑ z, |μ z * V (f z) - μ z * V (g z)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, μ z * |V (f z) - V (g z)| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hμ z)]
    _ ≤ ∑ z, μ z * (D * disagree f g z) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (hμ z)
    _ = ∑ z, D * (μ z * disagree f g z) := by
        refine Finset.sum_congr rfl fun z _ => ?_; ring

/-- **The event form**: the credence of any event moves by at most the disagreement mass;
total variation is a lower bound on the pathwise defect, never the other way. -/
theorem abs_expect_event_sub_le (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (A : Y → Bool)
    (f g : Z → Y) :
    |expectR μ (fun z => indR (A (f z))) - expectR μ (fun z => indR (A (g z)))|
      ≤ expectR μ (disagree f g) := by
  have h := abs_expect_sub_le_width μ hμ (fun y => indR (A y)) 1
    (fun y y' => by
      have := indR_nonneg (A y); have := indR_le_one (A y)
      have := indR_nonneg (A y'); have := indR_le_one (A y')
      rw [abs_le]; constructor <;> linarith) f g
  simpa using h

/-- **The mismatch mass is at most the two activation defects.** -/
theorem expect_mismatch_le_defects (β : Q → Z → Ω) (x : Ω → X) (c : Ω → Bool)
    (κ : X → Z → Bool) (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (qr qc : Q)
    (hx : ∀ z, x (β qr z) = x (β qc z)) :
    expectR μ (fun z => indR (c (β qr z)) * (1 - indR (c (β qc z))))
      ≤ expectR μ (defect β x c κ qr) + expectR μ (defect β x c κ qc) := by
  refine le_trans ?_ (expect_disagree_le β x c κ μ hμ qr qc hx)
  unfold expectR
  refine Finset.sum_le_sum fun z _ => ?_
  have h := mismatch_le_disagree (fun z => c (β qr z)) (fun z => c (β qc z)) z
  exact mul_le_mul_of_nonneg_left h (hμ z)

/-- **The bypass bound with the mismatch term charged to activation transparency.**
`security_bypass_le_mismatch` with `D · E[M] ≤ D · (τ_raw + τ_corr)`. -/
theorem security_bypass_le_defects (β : Q → Z → Ω) (x : Ω → X) (c : Ω → Bool)
    (κ : X → Z → Bool) (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (D L : ℝ) (hD : 0 ≤ D)
    (qr qc : Q) (hx : ∀ z, x (β qr z) = x (β qc z))
    (Vr Vapp Vl δ ρ : Z → ℝ)
    (hVr : ∀ z, Vr z ≤ D) (hVl : ∀ z, 0 ≤ Vl z)
    (hlip : ∀ z, c (β qr z) = true → c (β qc z) = true → |Vr z - Vapp z| ≤ L * δ z)
    (hρ : ∀ z, c (β qr z) = true → c (β qc z) = true → Vapp z - Vl z ≤ ρ z) :
    expectR μ (fun z => indR (c (β qr z)) * Vr z) - expectR μ (fun z => indR (c (β qc z)) * Vl z)
      ≤ L * expectR μ (fun z => indR (c (β qr z)) * indR (c (β qc z)) * δ z)
        + expectR μ (fun z => indR (c (β qr z)) * indR (c (β qc z)) * ρ z)
        + D * (expectR μ (defect β x c κ qr) + expectR μ (defect β x c κ qc)) := by
  have h := security_bypass_le_mismatch μ hμ D L Vr Vapp Vl δ ρ (fun z => c (β qr z))
    (fun z => c (β qc z)) hVr hVl hlip hρ
  beta_reduce at h
  have hM := expect_mismatch_le_defects β x c κ μ hμ qr qc hx
  have := mul_le_mul_of_nonneg_left hM hD
  linarith

end Approximate

/-! ## 6. The posterior corollary -/

/-- Under `Realizes`, an output's likelihood under any audited continuation is its
reference likelihood. -/
theorem likelihood_iff (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (D : Set Q)
    (h : Realizes β x f κ D) (q : Q) (hq : q ∈ D) (z : Z) (y : Y) :
    f (β q z) = y ↔ κ (x (β q z)) z = y := by
  rw [h q hq z]

/-- **Posterior transparency for every prior.**  The unnormalized posterior weight of `(q, z)`
given the output `y` is the same whether computed with the actual or the reference
likelihood; hence so is every normalized posterior and every conditional expectation. -/
theorem posterior_weight_eq [DecidableEq Y] (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y)
    (κ : X → Z → Y) (D : Set Q) (h : Realizes β x f κ D) (μ : Q → Z → ℝ) (y : Y)
    (q : Q) (hq : q ∈ D) (z : Z) :
    μ q z * (if f (β q z) = y then 1 else 0) = μ q z * (if κ (x (β q z)) z = y then 1 else 0) := by
  rw [h q hq z]

/-! ## 7. The amendment tower -/

/-- **Higher-order transparency.**  With a fixed floor and each level the declared amendment
of the level below from declared grounds and an authorized event, two continuations agreeing
on the declared amendment inputs below level `t` have the same specification at `t`. -/
theorem tower_factor {C G E : Type*} (β : Q → Z → Ω) (D : Set Q) (Amend : C → G → E → C)
    (spec : ℕ → Ω → C) (g : ℕ → Ω → G) (e : ℕ → Ω → E) (c₀ : C)
    (h0 : ∀ q ∈ D, ∀ z, spec 0 (β q z) = c₀)
    (hstep : ∀ t, ∀ q ∈ D, ∀ z,
      spec (t + 1) (β q z) = Amend (spec t (β q z)) (g t (β q z)) (e t (β q z))) :
    ∀ t, ∀ q ∈ D, ∀ q' ∈ D, ∀ z,
      (∀ s < t, g s (β q z) = g s (β q' z) ∧ e s (β q z) = e s (β q' z)) →
      spec t (β q z) = spec t (β q' z) := by
  intro t
  induction t with
  | zero => intro q hq q' hq' z _; rw [h0 q hq z, h0 q' hq' z]
  | succ t ih =>
      intro q hq q' hq' z hagree
      rw [hstep t q hq z, hstep t q' hq' z]
      have hlt : t < t + 1 := Nat.lt_succ_self t
      rw [ih q hq q' hq' z (fun s hs => hagree s (lt_trans hs hlt)),
        (hagree t hlt).1, (hagree t hlt).2]

/-! ## 8. Witnesses -/

namespace Witness

/-- **Cherry-picking is a selection failure.**  Worlds carry the true reasons `for` and
`against`; the honest continuation presents both, the picker presents `for`; the declared
input is the world's fact set, the same for both.  The picker does not realize the full
reference; it realizes the reference that declares its selection rule; and the two-element
class is not transparent at all. -/
inductive Q₁
  | honest
  | picker
  deriving DecidableEq

def β₁ : Q₁ → Unit → Q₁ × Finset ℕ := fun q _ => (q, {0, 1})

def x₁ : Q₁ × Finset ℕ → Finset ℕ := Prod.snd

def R₁ : Q₁ × Finset ℕ → Finset ℕ
  | (Q₁.honest, s) => s
  | (Q₁.picker, _) => {0}

def κfull : Finset ℕ → Unit → Finset ℕ := fun s _ => s
def κfirst : Finset ℕ → Unit → Finset ℕ := fun _ _ => {0}

theorem picker :
    Realizes β₁ x₁ R₁ κfull {Q₁.honest} ∧ ¬ Realizes β₁ x₁ R₁ κfull {Q₁.picker} ∧
    Realizes β₁ x₁ R₁ κfirst {Q₁.picker} ∧ ¬ Transparent β₁ x₁ R₁ {Q₁.honest, Q₁.picker} := by
  refine ⟨fun q hq z => ?_, fun h => ?_, fun q hq z => ?_, fun h => ?_⟩
  · simp only [Set.mem_singleton_iff] at hq; subst hq; rfl
  · have := h Q₁.picker rfl ()
    simp only [β₁, x₁, R₁, κfull] at this
    exact absurd this (by decide)
  · simp only [Set.mem_singleton_iff] at hq; subst hq; rfl
  · have := h () Q₁.honest (by simp) Q₁.picker (by simp) rfl
    simp only [β₁, R₁] at this
    exact absurd this (by decide)

/-- **A hidden read is a transparency failure**: the same declared input, a trace that reads
an undeclared source. -/
def β₂ : Bool → Unit → Bool := fun q _ => q

theorem hidden_read : ¬ Transparent β₂ (fun _ => ()) (fun w => w) {true, false} := by
  intro h
  have := h () true (by simp) false (by simp) rfl
  simp [β₂] at this

open Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness in
/-- **Two kinds of selection leak.**  Under `leakPol` the selection reaches the trace through
the declared other input: transparent, and the declared input is not selection-blind.  A
trace reading the selection coordinate itself is not transparent to the other input. -/
theorem leak_kinds :
    Realizes βₗ Rₗ Rₗ (fun a _ => a) Set.univ ∧
    ¬ (∀ σ σ', Rₗ (βₗ (leakPol σ) ()) = Rₗ (βₗ (leakPol σ') ())) ∧
    (∀ σ σ', Rₗ (βₗ (sealedPol σ) ()) = Rₗ (βₗ (sealedPol σ') ())) ∧
    ¬ Transparent βₗ Rₗ Prod.fst {(true, false), (false, false)} := by
  refine ⟨fun q _ z => rfl, fun h => ?_, fun σ σ' => rfl, fun h => ?_⟩
  · have := h true false
    simp [βₗ, Rₗ, leakPol] at this
  · have := h () (true, false) (by simp) (false, false) (by simp) rfl
    simp [βₗ] at this

/-- **The mismatch bound is inhabited and the defect charge is sharp on one world**: raw
activates, the corrigibilized option does not, the reference agrees with the corrigibilized
option; mismatch `1`, defects `1 + 0`. -/
theorem defect_attained :
    indR true * (1 - indR false) = 1 ∧
    defect (fun (q : Bool) (_ : Unit) => q) (fun _ => ()) (fun b => b) (fun _ _ => false)
      true () = 1 ∧
    defect (fun (q : Bool) (_ : Unit) => q) (fun _ => ()) (fun b => b) (fun _ _ => false)
      false () = 0 := by
  refine ⟨by norm_num [indR], by simp [defect, disagree], by simp [defect, disagree]⟩

/-- The tower theorem is inhabited: a specification counting authorized amendments, two
continuations, the same declared amendment inputs. -/
theorem tower_inhabited (q q' : Bool) :
    (fun (t : ℕ) (_ : Bool × ℕ) => t) 2 ((fun (q : Bool) (_ : Unit) => (q, 0)) q ())
      = (fun (t : ℕ) (_ : Bool × ℕ) => t) 2 ((fun (q : Bool) (_ : Unit) => (q, 0)) q' ()) :=
  tower_factor (fun (q : Bool) (_ : Unit) => (q, 0)) Set.univ
    (fun (c : ℕ) (_ : Unit) (e : Bool) => if e then c + 1 else c) (fun t _ => t)
    (fun _ _ => ()) (fun _ _ => true) 0 (fun _ _ _ => rfl) (fun _ _ _ _ => by simp)
    2 q trivial q' trivial () (fun _ _ => ⟨rfl, rfl⟩)

end Witness

end Workspace.Deference.Contrib.TransparentChannel

#print axioms Workspace.Deference.Contrib.TransparentChannel.transparent_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.transparent_iff_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.realizes_of_injOn
#print axioms Workspace.Deference.Contrib.TransparentChannel.reasonMediated_comp
#print axioms Workspace.Deference.Contrib.TransparentChannel.oracle_replacement
#print axioms Workspace.Deference.Contrib.TransparentChannel.payload_factor
#print axioms Workspace.Deference.Contrib.TransparentChannel.blind_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.blind_payload_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.selectionBlind_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.activation_eq_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.mismatch_zero_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.disagree_le_add
#print axioms Workspace.Deference.Contrib.TransparentChannel.defect_eq_zero_of_realizes
#print axioms Workspace.Deference.Contrib.TransparentChannel.disagree_le_defects
#print axioms Workspace.Deference.Contrib.TransparentChannel.expect_disagree_le
#print axioms Workspace.Deference.Contrib.TransparentChannel.abs_expect_sub_le_width
#print axioms Workspace.Deference.Contrib.TransparentChannel.abs_expect_event_sub_le
#print axioms Workspace.Deference.Contrib.TransparentChannel.mismatch_le_disagree
#print axioms Workspace.Deference.Contrib.TransparentChannel.expect_mismatch_le_defects
#print axioms Workspace.Deference.Contrib.TransparentChannel.security_bypass_le_defects
#print axioms Workspace.Deference.Contrib.TransparentChannel.likelihood_iff
#print axioms Workspace.Deference.Contrib.TransparentChannel.posterior_weight_eq
#print axioms Workspace.Deference.Contrib.TransparentChannel.tower_factor
#print axioms Workspace.Deference.Contrib.TransparentChannel.Witness.picker
#print axioms Workspace.Deference.Contrib.TransparentChannel.Witness.hidden_read
#print axioms Workspace.Deference.Contrib.TransparentChannel.Witness.leak_kinds
#print axioms Workspace.Deference.Contrib.TransparentChannel.Witness.defect_attained
#print axioms Workspace.Deference.Contrib.TransparentChannel.Witness.tower_inhabited
