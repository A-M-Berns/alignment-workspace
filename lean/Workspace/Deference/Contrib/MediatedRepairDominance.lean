/-
# Mediated repair dominance: the kernel

Round `projects/deference/rounds/2026-09-09-mediated-repair-dominance/`.

Finite algebra, each piece the mathematical core of one theorem of the round; the
interactive model that instantiates them is the round's `src/world.py`.  The pressure pass
(second dispatch) added §2a, §3a, §3b and their witnesses.

**1. Forcing is monotone along residual-frame morphisms.**  Fix the agent's continuation;
what remains is a Cartesian frame for the principal — `Agent` its continuations, `Env` the
exterior's, `outcome` the interaction map.  A frame morphism from the raw residual frame to
the lifted one (`CartesianFrameBridge.Frame.Hom`, mirrored from the authoritative library)
whose agent component is "approve" and whose environment component is the identity *is*
the exact approval-reproduction property.  `ensures_mono` says every set the principal
could force under the raw continuation it can force under the lift: principal-option
dominance in the frame register, with no value anywhere.

**2. Principal-option dominance in value.**  `sup'_le_sup'_add`: if every raw option is
reproduced by some lifted option up to `κ`, the lifted optimum is at least the raw optimum
less `κ`.  `option_dominance_expect`: pointwise `W_raw ≤ W_approve + κ` and
`W_approve ≤ W_actual + ρ` give the expectation bound with the principal's decision error
`ρ` charged where it is incurred.

**2a. The mediation gap from a structural certificate.**  `κ` as a measured gap makes
`W_raw ≤ W_approve + κ` true by definition.  `mediationGap_le_of_lipschitz` derives it: a
declared protected discrepancy `δ` between the raw and the approved trajectories and an
`L`-stable protected value give `(W_raw − W_approve)₊ ≤ L·δ`;
`option_dominance_of_approx_reproduction` is T2 with `L·E[δ]` in place of `E[κ]`, from
independent hypotheses.

**3a. Common activation.**  The canonical legitimate-deference theorem has one
activation event for the whole issued menu.  `bypass_premium_le_common`: with one `c`,
completions in a band of width `D`, and dominance needed only where `c` holds,

  `E[B_raw] − E[B_lift] ≤ E[κ] + E[ρ] + D · void(c)`

— one void term, not two, because both completions lie in one interval on the common void
branch (`Witness.commonVoid` attains it).  Common activation is well-typed only where the
evaluation's fate does not depend on which option is selected; that is a causal
requirement on the evaluation process, stated in the round's documents, not a theorem.

**3b. Security scores.**  `security_score_bypass_le`: the activated securities' expectations
themselves satisfy `E[c·V_raw] − E[c·V_lift] ≤ E[κ] + E[ρ]` — no completion, no void term;
`security_score_bypass_le_of_prices` adds price calibration; `operative_choice_loss` is the
chooser algebra: a chooser that rates the raw option within `ε` of the lift by those scores
loses at most `ε` plus calibration in activated protected value.

**3. The bypass premium in the activated register, per option.**  `bypass_premium_le`: the agent's
operative values are completions of the activated protected evaluations of the two options
(agree with them where the evaluation activates, lie in the band elsewhere).  Then

  `E[B_raw] − E[B_lift] ≤ E[κ] + E[ρ] + D · void(raw) + D · void(lift)`.

`Witness.totalVoid` attains the void term with `κ = ρ = 0`: a violation that ends the
evaluation is invisible to the activated register exactly in proportion to the void mass it
creates, and a completion at the top of the band rates it at `D`.  `deferential_bypass_loss`
is the selection form: an agent whose selection has activated regret `ε` loses at most
`ε + D · void(lift)` in protected value against the lift, for any completion.

**4. The refused route.**  `mediation_st_iff_ct`: bounding the premium by selected trust at
the mediation cells — the agent's operative gain from the effect over the decline, net of the
principal's, on the cells where the principal declines — is *identically* the incentive
round's `(CT)` with the lift as the repair.  `SelectedTrustNonPreemption.ct_strictly_stronger`
therefore applies to it verbatim, and the round does not take that route.

**What this does not establish.**  That any physical continuation has a lift (the model
supplies it by interposition on a declared effect interface, and containment is external);
that a common activation event exists for a menu containing an evaluator-destroying
option (it does not, and the round says where); that the agent's operative selection is
by activated securities rather than by a completion (the `(DV)` bridge, item 84, needed
only for a latent total value); anything about `ρ` beyond charging it.  Names are
provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.CartesianFrameBridge
import Workspace.Deference.Contrib.ActivatedValue
import Workspace.Deference.Contrib.SelectedTrustNonPreemption

namespace Workspace.Deference.Contrib.MediatedRepairDominance

open Workspace.Deference.Contrib.CartesianFrameBridge (Frame)

/-- Expectation under a credence (`ActivatedValue.expect`, unambiguous name). -/
abbrev expect {X : Type*} [Fintype X] (μ X' : X → ℚ) : ℚ :=
  Workspace.Deference.Contrib.ActivatedValue.expect μ X'

/-- The activation indicator (`ActivatedValue.ind`). -/
abbrev ind {X : Type*} (c : X → Bool) (x : X) : ℚ :=
  Workspace.Deference.Contrib.ActivatedValue.ind c x

theorem ind_nonneg {X : Type*} (c : X → Bool) (x : X) : 0 ≤ ind c x :=
  Workspace.Deference.Contrib.ActivatedValue.ind_nonneg c x

theorem ind_le_one {X : Type*} (c : X → Bool) (x : X) : ind c x ≤ 1 :=
  Workspace.Deference.Contrib.ActivatedValue.ind_le_one c x

/-! ## 1. Forcing along residual-frame morphisms -/

section Frames

universe u
variable {W : Type u}

/-- The principal, holding the agent side of the residual frame `C`, can force the
outcome into `S` against every exterior continuation. -/
def Ensures (C : Frame W) (S : Set W) : Prop := ∃ a, ∀ e, C.outcome a e ∈ S

/-- **Forcing is monotone along frame morphisms.**  A morphism from the raw residual
frame to the lifted one transports every forcing strategy: `approve ∘ p` forces in the
lift whatever `p` forced in the raw frame.  With the environment component the identity
this is exactly approval reproduction; the theorem needs only the adjoint equation. -/
theorem ensures_mono {C D : Frame W} (f : Frame.Hom C D) {S : Set W}
    (h : Ensures C S) : Ensures D S := by
  obtain ⟨a, ha⟩ := h
  exact ⟨f.agent a, fun e => by rw [← f.adjoint a e]; exact ha (f.env e)⟩

/-- Exact approval reproduction over a shared exterior: the lifted frame has, for every
raw principal continuation, an approving continuation with the same outcome map.  It is
a frame morphism with identity environment component. -/
def approvalMorphism (C D : Frame W) (approve : C.Agent → D.Agent) (hE : D.Env = C.Env)
    (h : ∀ p e, C.outcome p (cast hE e) = D.outcome (approve p) e) : Frame.Hom C D where
  agent := approve
  env := fun e => cast hE e
  adjoint := h

end Frames

/-! ## 2. Principal-option dominance in value -/

section Dominance

/-- **Option extension.**  If every raw option is reproduced by some lifted option up to
`κ`, the lifted optimum is at least the raw optimum less `κ`. -/
theorem sup'_le_sup'_add {ι κι : Type*} {S : Finset ι} {S' : Finset κι}
    (hS : S.Nonempty) (hS' : S'.Nonempty) (f : ι → ℚ) (g : κι → ℚ) (k : ℚ)
    (h : ∀ i ∈ S, ∃ j ∈ S', f i ≤ g j + k) :
    S.sup' hS f ≤ S'.sup' hS' g + k := by
  rw [Finset.sup'_le_iff]
  intro i hi
  obtain ⟨j, hj, hij⟩ := h i hi
  have := Finset.le_sup' g hj
  linarith

variable {X : Type*} [Fintype X]

/-- **Principal-option dominance, pointwise form.**  In each world the raw protected value
is within `κ` of the approve branch (reproduction) and the approve branch is within `ρ` of
the principal's actual decision (decision error, zero where declining was right).  Then in
expectation `W_raw ≤ W_actual + E[κ] + E[ρ]`.  No corrigibility bonus appears: the only
inputs are reproduction and the principal's own decision. -/
theorem option_dominance_expect (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (Wraw Wapp Wact κ ρ : X → ℚ)
    (hκ : ∀ x, Wraw x - Wapp x ≤ κ x) (hρ : ∀ x, Wapp x - Wact x ≤ ρ x) :
    expect μ Wraw ≤ expect μ Wact + expect μ κ + expect μ ρ := by
  have : expect μ Wact + expect μ κ + expect μ ρ
      = ∑ x, μ x * (Wact x + κ x + ρ x) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]
  unfold expect Workspace.Deference.Contrib.ActivatedValue.expect
  refine Finset.sum_le_sum fun x _ => ?_
  have := hκ x
  have := hρ x
  nlinarith [hμ x]

/-- The exact case: reproduction is exact and the principal never declines what it should
have approved, so the lift weakly dominates. -/
theorem option_dominance_exact (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (Wraw Wapp Wact : X → ℚ)
    (hκ : ∀ x, Wraw x ≤ Wapp x) (hρ : ∀ x, Wapp x ≤ Wact x) :
    expect μ Wraw ≤ expect μ Wact := by
  have h := option_dominance_expect μ hμ Wraw Wapp Wact (fun _ => 0) (fun _ => 0)
    (fun x => by linarith [hκ x]) (fun x => by linarith [hρ x])
  simpa [expect, Workspace.Deference.Contrib.ActivatedValue.expect] using h

/-- **The mediation gap from a structural certificate.**  A protected discrepancy `δ`
between the raw and the approved projections and an `L`-stable protected value bound the
positive gap by `L · δ`.  `κ` is then derived, not measured. -/
theorem mediationGap_le_of_lipschitz (L δ wraw wapp : ℚ)
    (hlip : |wraw - wapp| ≤ L * δ) : max (wraw - wapp) 0 ≤ L * δ := by
  have h1 : wraw - wapp ≤ L * δ := le_trans (le_abs_self _) hlip
  have h2 : (0 : ℚ) ≤ L * δ := le_trans (abs_nonneg _) hlip
  exact max_le h1 h2

/-- **Principal-option dominance from approximate reproduction.**  Pointwise
`|W_raw − W_approve| ≤ L · δ` (structural reproduction certificate plus stability) and
decline regret `ρ` give `E[W_raw] ≤ E[W_actual] + L · E[δ] + E[ρ]` — T2 from independent
hypotheses, with the measured `κ` nowhere. -/
theorem option_dominance_of_approx_reproduction (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (L : ℚ) (Wraw Wapp Wact δ ρ : X → ℚ)
    (hlip : ∀ x, |Wraw x - Wapp x| ≤ L * δ x) (hρ : ∀ x, Wapp x - Wact x ≤ ρ x) :
    expect μ Wraw ≤ expect μ Wact + L * expect μ δ + expect μ ρ := by
  have h := option_dominance_expect μ hμ Wraw Wapp Wact (fun x => L * δ x) ρ
    (fun x => le_trans (le_abs_self _) (hlip x)) hρ
  have : expect μ (fun x => L * δ x) = L * expect μ δ := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  linarith

end Dominance

/-! ## 3a. Common activation and security scores -/

section Common

variable {X : Type*} [Fintype X]

/-- **The bypass premium under one common activation event.**  One `c` for the issued
menu; completions `B_raw, B_lift` in the band `[lo, lo + D]` agreeing with the
evaluations where `c` holds; nonnegative `κ, ρ` with dominance required on the activated
worlds only.  Then `E[B_raw] − E[B_lift] ≤ E[κ] + E[ρ] + D · void(c)`: a single void term,
because on the common void branch both completions lie in one interval of width `D`. -/
theorem bypass_premium_le_common (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (lo D : ℚ)
    (Vr Vl Br Bl κ ρ : X → ℚ) (c : X → Bool)
    (hBr : ∀ x, lo ≤ Br x ∧ Br x ≤ lo + D) (hBl : ∀ x, lo ≤ Bl x ∧ Bl x ≤ lo + D)
    (hcr : ∀ x, c x = true → Br x = Vr x) (hcl : ∀ x, c x = true → Bl x = Vl x)
    (hκ : ∀ x, 0 ≤ κ x) (hρ : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x, c x = true → Vr x ≤ Vl x + κ x + ρ x) :
    expect μ Br - expect μ Bl ≤ expect μ κ + expect μ ρ + D * expect μ (fun x => 1 - ind c x) := by
  have hpt : ∀ x, Br x - Bl x ≤ κ x + ρ x + D * (1 - ind c x) := by
    intro x
    unfold ind Workspace.Deference.Contrib.ActivatedValue.ind
    by_cases h : c x = true
    · have := hdom x h
      rw [hcr x h, hcl x h]
      simp only [h, if_true]
      linarith
    · have h' : c x = false := by simpa using h
      simp only [h', Bool.false_eq_true, if_false, sub_zero, mul_one]
      linarith [(hBr x).2, (hBl x).1, hκ x, hρ x]
  have hrhs : expect μ κ + expect μ ρ + D * expect μ (fun x => 1 - ind c x)
      = ∑ x, μ x * (κ x + ρ x + D * (1 - ind c x)) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hlhs : expect μ Br - expect μ Bl = ∑ x, μ x * (Br x - Bl x) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrhs, hlhs]
  refine Finset.sum_le_sum fun x _ => ?_
  exact mul_le_mul_of_nonneg_left (hpt x) (hμ x)

/-- **Security scores need no completion.**  The activated securities' expectations satisfy
the bypass bound with no void term: `E[c · V_raw] − E[c · V_lift] ≤ E[κ] + E[ρ]`, with
dominance needed on the activated worlds only. -/
theorem security_score_bypass_le (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (Vr Vl κ ρ : X → ℚ) (c : X → Bool)
    (hκ : ∀ x, 0 ≤ κ x) (hρ : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x, c x = true → Vr x ≤ Vl x + κ x + ρ x) :
    expect μ (fun x => ind c x * Vr x) - expect μ (fun x => ind c x * Vl x)
      ≤ expect μ κ + expect μ ρ := by
  have hpt : ∀ x, ind c x * Vr x - ind c x * Vl x ≤ κ x + ρ x := by
    intro x
    unfold ind Workspace.Deference.Contrib.ActivatedValue.ind
    by_cases h : c x = true
    · have := hdom x h
      simp only [h, if_true, one_mul]
      linarith
    · have h' : c x = false := by simpa using h
      simp only [h', Bool.false_eq_true, if_false, zero_mul, sub_zero]
      linarith [hκ x, hρ x]
  have hrhs : expect μ κ + expect μ ρ = ∑ x, μ x * (κ x + ρ x) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hlhs : expect μ (fun x => ind c x * Vr x) - expect μ (fun x => ind c x * Vl x)
      = ∑ x, μ x * (ind c x * Vr x - ind c x * Vl x) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrhs, hlhs]
  refine Finset.sum_le_sum fun x _ => ?_
  exact mul_le_mul_of_nonneg_left (hpt x) (hμ x)

/-- The same for prices within `ε_r`, `ε_l` of the securities' expectations: the
security-score bypass incentive is at most `E[κ] + E[ρ] + ε_r + ε_l`. -/
theorem security_score_bypass_le_of_prices (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (Vr Vl κ ρ : X → ℚ) (c : X → Bool) (Pr Pl εr εl : ℚ)
    (hκ : ∀ x, 0 ≤ κ x) (hρ : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x, c x = true → Vr x ≤ Vl x + κ x + ρ x)
    (hPr : Pr - expect μ (fun x => ind c x * Vr x) ≤ εr)
    (hPl : expect μ (fun x => ind c x * Vl x) - Pl ≤ εl) :
    Pr - Pl ≤ expect μ κ + expect μ ρ + εr + εl := by
  have := security_score_bypass_le μ hμ Vr Vl κ ρ c hκ hρ hdom
  linarith

/-- **Operative choice.**  A chooser whose scores at the mediation cell are within `ε_cal`
of the securities' expectations and which selects the raw option only when its score is
within `ε` of the lift's loses at most `ε + 2 ε_cal` of activated protected value by that
choice.  Algebra: the by-construction chooser's bypass incentive is its score gap. -/
theorem operative_choice_loss (Ur Ul Sr Sl ε εcal : ℚ)
    (hSr : |Sr - Ur| ≤ εcal) (hSl : |Sl - Ul| ≤ εcal) (hchoose : Sl - Sr ≤ ε) :
    Ul - Ur ≤ ε + 2 * εcal := by
  have h1 := abs_le.mp hSr
  have h2 := abs_le.mp hSl
  linarith [h1.1, h1.2, h2.1, h2.2]

end Common

/-! ## 3. The bypass premium in the activated register, per option -/

section Premium

variable {X : Type*} [Fintype X]

omit [Fintype X] in
/-- A completion's excess over the activated evaluation is zero where the evaluation
activates and at most the band width `D` where it does not. -/
theorem completion_excess_le (lo D : ℚ) (V B : X → ℚ) (c : X → Bool)
    (hV : ∀ x, lo ≤ V x ∧ V x ≤ lo + D) (hB : ∀ x, lo ≤ B x ∧ B x ≤ lo + D)
    (hc : ∀ x, c x = true → B x = V x) (x : X) :
    B x - V x ≤ D * (1 - ind c x) := by
  unfold ind Workspace.Deference.Contrib.ActivatedValue.ind
  by_cases h : c x = true
  · simp [h, hc x h]
  · have h' : c x = false := by simpa using h
    simp only [h', Bool.false_eq_true, if_false, sub_zero, mul_one]
    linarith [(hV x).1, (hB x).2]

/-- **The bypass premium.**  `V_raw, V_lift` the protected evaluations of the two options
per world, `c_raw, c_lift` their activations, `B_raw, B_lift` the agent's operative values —
completions of the activated evaluations in the band `[lo, lo + D]` — and pointwise
dominance `V_raw ≤ V_lift + κ + ρ`.  Then

  `E[B_raw] − E[B_lift] ≤ E[κ] + E[ρ] + D · void(raw) + D · void(lift)`.

The two void terms are the only place the agent's values off the activated support enter;
they are the completion theorem's slack, one-sided per option. -/
theorem bypass_premium_le (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (lo D : ℚ)
    (Vr Vl Br Bl κ ρ : X → ℚ) (cr cl : X → Bool)
    (hVr : ∀ x, lo ≤ Vr x ∧ Vr x ≤ lo + D) (hVl : ∀ x, lo ≤ Vl x ∧ Vl x ≤ lo + D)
    (hBr : ∀ x, lo ≤ Br x ∧ Br x ≤ lo + D) (hBl : ∀ x, lo ≤ Bl x ∧ Bl x ≤ lo + D)
    (hcr : ∀ x, cr x = true → Br x = Vr x) (hcl : ∀ x, cl x = true → Bl x = Vl x)
    (hdom : ∀ x, Vr x ≤ Vl x + κ x + ρ x) :
    expect μ Br - expect μ Bl
      ≤ expect μ κ + expect μ ρ
        + D * expect μ (fun x => 1 - ind cr x) + D * expect μ (fun x => 1 - ind cl x) := by
  have hpt : ∀ x, Br x - Bl x
      ≤ κ x + ρ x + D * (1 - ind cr x) + D * (1 - ind cl x) := by
    intro x
    have h1 := completion_excess_le lo D Vr Br cr hVr hBr hcr x
    have h2 : Vl x - Bl x ≤ D * (1 - ind cl x) := by
      unfold ind Workspace.Deference.Contrib.ActivatedValue.ind
      by_cases h : cl x = true
      · simp [h, hcl x h]
      · have h' : cl x = false := by simpa using h
        simp only [h', Bool.false_eq_true, if_false, sub_zero, mul_one]
        linarith [(hVl x).2, (hBl x).1]
    have h3 := hdom x
    linarith
  have hrhs : expect μ κ + expect μ ρ
      + D * expect μ (fun x => 1 - ind cr x) + D * expect μ (fun x => 1 - ind cl x)
      = ∑ x, μ x * (κ x + ρ x + D * (1 - ind cr x) + D * (1 - ind cl x)) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrhs]
  have hlhs : expect μ Br - expect μ Bl = ∑ x, μ x * (Br x - Bl x) := by
    simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hlhs]
  refine Finset.sum_le_sum fun x _ => ?_
  exact mul_le_mul_of_nonneg_left (hpt x) (hμ x)

/-- The same with the agent's operative values known only up to `ε`. -/
theorem bypass_premium_le_of_approx (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (lo D : ℚ)
    (Vr Vl Br Bl κ ρ : X → ℚ) (cr cl : X → Bool) (Ar Al εr εl : ℚ)
    (hVr : ∀ x, lo ≤ Vr x ∧ Vr x ≤ lo + D) (hVl : ∀ x, lo ≤ Vl x ∧ Vl x ≤ lo + D)
    (hBr : ∀ x, lo ≤ Br x ∧ Br x ≤ lo + D) (hBl : ∀ x, lo ≤ Bl x ∧ Bl x ≤ lo + D)
    (hcr : ∀ x, cr x = true → Br x = Vr x) (hcl : ∀ x, cl x = true → Bl x = Vl x)
    (hdom : ∀ x, Vr x ≤ Vl x + κ x + ρ x)
    (hAr : Ar - expect μ Br ≤ εr) (hAl : expect μ Bl - Al ≤ εl) :
    Ar - Al
      ≤ expect μ κ + expect μ ρ
        + D * expect μ (fun x => 1 - ind cr x) + D * expect μ (fun x => 1 - ind cl x)
        + εr + εl := by
  have := bypass_premium_le μ hμ lo D Vr Vl Br Bl κ ρ cr cl hVr hVl hBr hBl hcr hcl hdom
  linarith

/-- **Selection form.**  Values in `[0, D]`; the agent selects the option whose activated
security it rates higher, up to `ε`; the lift's evaluation is void with mass at most
`η_l`.  Then whichever option is selected loses at most `ε + D · η_l` in (completed)
protected value against the lift.  The raw option's void mass does not appear: a
selection by activated securities already rates a voiding option at its activated value.
What the bound says on void worlds is exactly what the completion says there. -/
theorem deferential_bypass_loss (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (D : ℚ) (hD : 0 ≤ D)
    (Vsel Vl : X → ℚ) (csel cl : X → Bool) (ε ηl : ℚ)
    (hVsel : ∀ x, 0 ≤ Vsel x ∧ Vsel x ≤ D) (hVl : ∀ x, 0 ≤ Vl x ∧ Vl x ≤ D)
    (hηl : expect μ (fun x => 1 - ind cl x) ≤ ηl)
    (hsel : expect μ (fun x => ind cl x * Vl x) - expect μ (fun x => ind csel x * Vsel x) ≤ ε) :
    expect μ Vl - expect μ Vsel ≤ ε + D * ηl := by
  -- the lift's unactivated excess is at most D · void(lift)
  have h1 : expect μ Vl - expect μ (fun x => ind cl x * Vl x)
      ≤ D * expect μ (fun x => 1 - ind cl x) := by
    have : expect μ Vl - expect μ (fun x => ind cl x * Vl x)
        = ∑ x, μ x * ((1 - ind cl x) * Vl x) := by
      simp only [expect, Workspace.Deference.Contrib.ActivatedValue.expect, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [this]
    unfold expect Workspace.Deference.Contrib.ActivatedValue.expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h1c : 0 ≤ 1 - ind cl x := by linarith [ind_le_one cl x]
    have := mul_le_mul_of_nonneg_left (hVl x).2 h1c
    nlinarith [hμ x]
  -- the selection's activated value is at most its value
  have h2 : expect μ (fun x => ind csel x * Vsel x) ≤ expect μ Vsel := by
    unfold expect Workspace.Deference.Contrib.ActivatedValue.expect
    refine Finset.sum_le_sum fun x _ => ?_
    show μ x * (ind csel x * Vsel x) ≤ μ x * Vsel x
    have h1 := ind_le_one csel x
    have h0 := (hVsel x).1
    have : ind csel x * Vsel x ≤ Vsel x := by nlinarith
    exact mul_le_mul_of_nonneg_left this (hμ x)
  have h3 := mul_le_mul_of_nonneg_left hηl hD
  linarith

end Premium

/-! ## 4. The refused route: selected trust at the mediation cells is `(CT)` -/

section Refused

variable {C : Type*} [Fintype C]

/-- The agent's value of executing the effect everywhere (the raw continuation). -/
def rawVal (p : C → ℚ) (E : C → ℚ) : ℚ := ∑ x, p x * E x

/-- The value of the lifted continuation under the principal's decision `J` (`true` =
approve): the effect's value where approved, the decline's where declined. -/
def liftVal (p : C → ℚ) (J : C → Bool) (Ee Ed : C → ℚ) : ℚ :=
  ∑ x, p x * (if J x then Ee x else Ed x)

/-- Selected trust at the mediation cells: on the cells where the principal declines,
the agent's operative preference for the effect over the decline, net of the
principal's, credence-weighted. -/
def declGap (p : C → ℚ) (J : C → Bool) (EXe EXd We Wd : C → ℚ) : ℚ :=
  ∑ x, p x * (if J x then 0 else (EXe x - EXd x) - (We x - Wd x))

/-- The principal's regret of declining, credence-weighted. -/
def declRegret (p : C → ℚ) (J : C → Bool) (We Wd : C → ℚ) : ℚ :=
  ∑ x, p x * (if J x then 0 else We x - Wd x)

/-- Under exact reproduction the premium at the mediation cells is the Level I identity:
selected gap plus the principal's regret of declining. -/
theorem premium_eq_gap_add_regret (p : C → ℚ) (J : C → Bool) (EXe EXd We Wd : C → ℚ) :
    rawVal p EXe - liftVal p J EXe EXd
      = declGap p J EXe EXd We Wd + declRegret p J We Wd := by
  simp only [rawVal, liftVal, declGap, declRegret, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- `X − Y = −gap` for `X` the agent's lift-minus-raw comparison and `Y` the principal's. -/
theorem lift_sub_raw_sub (p : C → ℚ) (J : C → Bool) (EXe EXd We Wd : C → ℚ) :
    (liftVal p J EXe EXd - rawVal p EXe) - (liftVal p J We Wd - rawVal p We)
      = - declGap p J EXe EXd We Wd := by
  simp only [liftVal, rawVal, declGap, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- **Selected trust at the mediation cells is `(CT)` with the lift as the repair.**  The
hypothesis `declGap ≤ ε` and the incentive round's `X − Y ≥ −ε` are the same inequality,
so `ct_strictly_stronger` applies to it verbatim: it is the conclusion `Φ ≤ ε` with the
principal's margin added, not a reduction. -/
theorem mediation_st_iff_ct (p : C → ℚ) (J : C → Bool) (EXe EXd We Wd : C → ℚ) (ε : ℚ) :
    declGap p J EXe EXd We Wd ≤ ε
      ↔ (liftVal p J EXe EXd - rawVal p EXe) - (liftVal p J We Wd - rawVal p We) ≥ -ε := by
  rw [lift_sub_raw_sub]
  constructor <;> intro h <;> linarith

end Refused

/-! ## 5. Witnesses -/

namespace Witness

/-- **Total void attains the bound.**  One world; the raw option ends the evaluation
(`c_raw = false`), the lift keeps it; both protected evaluations are `0`, reproduction is
exact and the principal errs nowhere; the agent's completion rates the void branch at the
top of the band.  Premium `D = 1`, and the bound's only nonzero term is `D · void(raw)`. -/
theorem totalVoid :
    let μ : Fin 1 → ℚ := fun _ => 1
    let Vr : Fin 1 → ℚ := fun _ => 0
    let Vl : Fin 1 → ℚ := fun _ => 0
    let Br : Fin 1 → ℚ := fun _ => 1
    let Bl : Fin 1 → ℚ := fun _ => 0
    let cr : Fin 1 → Bool := fun _ => false
    let cl : Fin 1 → Bool := fun _ => true
    expect μ Br - expect μ Bl = 1
      ∧ (1 : ℚ) * expect μ (fun x => 1 - ind cr x) = 1
      ∧ expect μ (fun x => 1 - ind cl x) = 0
      ∧ (∀ x, Vr x ≤ Vl x + 0 + 0)
      ∧ (∀ x, cr x = true → Br x = Vr x) ∧ (∀ x, cl x = true → Bl x = Vl x) := by
  simp [expect, ind, Workspace.Deference.Contrib.ActivatedValue.expect,
    Workspace.Deference.Contrib.ActivatedValue.ind]

/-- **Common void attains the single `D·η` term.**  One world, one common activation
event that fails, both evaluations `0`, `κ = ρ = 0`; the agent's completions at the two
ends of the band.  Premium `D = 1`, and the common bound is `D · void = 1` — where the
per-option bound with `c_raw = c_lift` would read `2`. -/
theorem commonVoid :
    let μ : Fin 1 → ℚ := fun _ => 1
    let Br : Fin 1 → ℚ := fun _ => 1
    let Bl : Fin 1 → ℚ := fun _ => 0
    let c : Fin 1 → Bool := fun _ => false
    expect μ Br - expect μ Bl = 1
      ∧ (1 : ℚ) * expect μ (fun x => 1 - ind c x) = 1
      ∧ (1 : ℚ) * expect μ (fun x => 1 - ind c x) + (1 : ℚ) * expect μ (fun x => 1 - ind c x) = 2 := by
  simp [expect, ind, Workspace.Deference.Contrib.ActivatedValue.expect,
    Workspace.Deference.Contrib.ActivatedValue.ind]
  norm_num

/-- **The Lipschitz certificate is attained.**  Two exterior paths; protected distance `0`
where the contract survives and `1` where it expired; `L = 4`; the measured gap is exactly
`L · δ` on every path and `E[κ] = L · E[δ] = 1`. -/
theorem tightLipschitz :
    let μ : Fin 2 → ℚ := ![3/4, 1/4]
    let Vr : Fin 2 → ℚ := ![4, 4]
    let Vl : Fin 2 → ℚ := ![4, 0]
    let δ : Fin 2 → ℚ := ![0, 1]
    (∀ x, |Vr x - Vl x| ≤ 4 * δ x) ∧ 4 * expect μ δ = 1 ∧ expect μ Vr - expect μ Vl = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; fin_cases x <;> simp
  · simp [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Fin.sum_univ_two]
  · simp [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Fin.sum_univ_two]

/-- **The mediation cost is attained.**  Two exterior paths: the opportunity stays
(`3/4`) or expires (`1/4`); the raw option signs at once (value `4` either way), the lift
signs after approval (value `4` or `0`).  Everything activates, the principal approves;
the premium is exactly `E[κ] = 1`. -/
theorem tightKappa :
    let μ : Fin 2 → ℚ := ![3/4, 1/4]
    let Vr : Fin 2 → ℚ := ![4, 4]
    let Vl : Fin 2 → ℚ := ![4, 0]
    let κ : Fin 2 → ℚ := ![0, 4]
    expect μ Vr - expect μ Vl = 1 ∧ expect μ κ = 1 ∧ (∀ x, Vr x ≤ Vl x + κ x + 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Fin.sum_univ_two]
  · simp [expect, Workspace.Deference.Contrib.ActivatedValue.expect, Fin.sum_univ_two]
  · intro x; fin_cases x <;> simp

end Witness

end Workspace.Deference.Contrib.MediatedRepairDominance

#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.ensures_mono
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.sup'_le_sup'_add
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.option_dominance_expect
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.option_dominance_exact
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.completion_excess_le
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.bypass_premium_le
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.bypass_premium_le_of_approx
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.deferential_bypass_loss
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.premium_eq_gap_add_regret
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.lift_sub_raw_sub
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.mediation_st_iff_ct
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.mediationGap_le_of_lipschitz
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.option_dominance_of_approx_reproduction
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.bypass_premium_le_common
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.security_score_bypass_le
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.security_score_bypass_le_of_prices
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.operative_choice_loss
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.Witness.totalVoid
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.Witness.commonVoid
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.Witness.tightLipschitz
#print axioms Workspace.Deference.Contrib.MediatedRepairDominance.Witness.tightKappa
