import Cleanroom.Corrigibility.CorrValueChange.Model
import Cleanroom.Corrigibility.CorrValueChange.Update

/-!
# corr-value-change — epistemicizing utility change (T5)

Source: [[value-change-as-epistemic-update]] §2.1–2.2. Candidate utilities `u_θ`, each assigning
to an act `a` a function `u_{θ,a} : Ω → ℝ`; the extended world `Ω⁺ = Ω × Θ`, the fixed extended
utility `U⁺_a(ω, θ) = u_{θ,a}(ω)`, an extended prior `P⁺` on `Ω⁺`, and the **effective utility**
`Ū_a(ω) = ∑_θ P⁺(θ ∣ ω) u_{θ,a}(ω)`. `Θ` is finite throughout (the note's "with `Θ` rich enough,
any target" is therefore a remark about choosing `Θ`, not a theorem here).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω Θ A : Type} [Fintype Ω] [Fintype Θ] [Fintype A] [DecidableEq Ω] [DecidableEq Θ]

/-- The extended utility `U⁺_a(ω, θ) = u_{θ,a}(ω)`, a single fixed function.
Source: [[value-change-as-epistemic-update]] §2.1
Kind: D
Fidelity: exact -/
def Uplus (u : Θ → A → Ω → ℝ) (a : A) (x : Ω × Θ) : ℝ := u x.2 a x.1

/-- The marginal of `P⁺` on `Ω`: `P̄(ω) = ∑_θ P⁺(ω, θ)`.
Source: [[value-change-as-epistemic-update]] §2.1
Kind: D
Fidelity: exact -/
def margΩ (Pp : Prob (Ω × Θ)) (ω : Ω) : ℝ := ∑ θ, Pp.p (ω, θ)

/-- The value posterior `P⁺(θ ∣ ω) = P⁺(ω, θ) / P̄(ω)` (junk `0` at `P̄(ω) = 0`; see
`marginalization` for why no junk leaks).
Source: [[value-change-as-epistemic-update]] §2.1
Kind: D
Fidelity: exact on `P̄(ω) > 0` -/
def post (Pp : Prob (Ω × Θ)) (θ : Θ) (ω : Ω) : ℝ := Pp.p (ω, θ) / margΩ Pp ω

/-- **The effective utility** `Ū_a(ω) = ∑_θ P⁺(θ ∣ ω) u_{θ,a}(ω)`: what the extended agent
maximizes on the original worlds — its current *representation* of its values.
Source: [[value-change-as-epistemic-update]] §2.1 (the display defining `Ū_a`)
Kind: D
Fidelity: exact -/
def effU (Pp : Prob (Ω × Θ)) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) : ℝ :=
  ∑ θ, post Pp θ ω * u θ a ω

/-- The effective utility of a posterior family `λ_θ(ω)` given directly: `∑_θ λ_θ(ω) u_{θ,a}(ω)`.
Source: [[value-change-as-epistemic-update]] §2.2 (`Ū'_a(ω) = ∑_θ Q(θ ∣ ω) u_{θ,a}(ω)`)
Kind: D
Fidelity: exact -/
def effUOf (lam : Θ → Ω → ℝ) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) : ℝ :=
  ∑ θ, lam θ ω * u θ a ω

/-- `P̄(ω) ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem margΩ_nonneg (Pp : Prob (Ω × Θ)) (ω : Ω) : 0 ≤ margΩ Pp ω :=
  sum_nonneg fun θ _ => Pp.nonneg (ω, θ)

/-- `∑_ω P̄(ω) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem margΩ_sum (Pp : Prob (Ω × Θ)) : ∑ ω, margΩ Pp ω = 1 := by
  unfold margΩ; rw [← Fintype.sum_prod_type']; exact Pp.sum_one

/-- The marginal as a `Prob Ω`.
Source: [[value-change-as-epistemic-update]] §2.1 (`P̄`)
Kind: D
Fidelity: exact -/
def margProb (Pp : Prob (Ω × Θ)) : Prob Ω where
  p := margΩ Pp
  nonneg := margΩ_nonneg Pp
  sum_one := margΩ_sum Pp

/-- `P⁺(ω, θ) = 0` where `P̄(ω) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pp_eq_zero_of_margΩ_eq_zero (Pp : Prob (Ω × Θ)) {ω : Ω} (h : margΩ Pp ω = 0) (θ : Θ) :
    Pp.p (ω, θ) = 0 :=
  (sum_eq_zero_iff_of_nonneg fun θ _ => Pp.nonneg (ω, θ)).1 h θ (mem_univ θ)

/-- **T5(a), marginalization (the tower property)**: for every act,
`E_{P⁺}[U⁺_a] = ∑_{(ω,θ)} P⁺(ω,θ) u_{θ,a}(ω) = ∑_ω P̄(ω) Ū_a(ω) = E_{P̄}[Ū_a]`. No positivity
hypothesis: at a world with `P̄(ω) = 0` every `P⁺(ω, θ)` vanishes, so both sides contribute `0`
there and the junk value of `Ū_a(ω)` is multiplied by `0`.
Source: [[value-change-as-epistemic-update]] §2.1 ("for every act `E_{P⁺}[U⁺_a] = E_{P̄}[Ū_a]`
… by the tower property")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem marginalization (Pp : Prob (Ω × Θ)) (u : Θ → A → Ω → ℝ) (a : A) :
    ∑ x, Pp.p x * Uplus u a x = ∑ ω, margΩ Pp ω * effU Pp u a ω := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  unfold effU post Uplus
  rw [mul_sum]
  refine sum_congr rfl fun θ _ => ?_
  rcases (margΩ_nonneg Pp ω).lt_or_eq with hpos | hzero
  · field_simp
  · rw [Pp_eq_zero_of_margΩ_eq_zero Pp hzero.symm θ, ← hzero]; simp

/-- The epistemicization determined by a decomposition: `P⁺(ω, θ) := P̄(ω) λ_θ(ω)`.
Source: [[value-change-as-epistemic-update]] §2.1 ("Kolmogorov → epistemicized is a choice of
decomposition")
Kind: D
Fidelity: exact -/
def ofDecomp (Pb : Prob Ω) (lam : Θ → Ω → ℝ) (hnn : ∀ θ ω, 0 ≤ lam θ ω)
    (hsum : ∀ ω, ∑ θ, lam θ ω = 1) : Prob (Ω × Θ) where
  p := fun x => Pb.p x.1 * lam x.2 x.1
  nonneg := fun x => mul_nonneg (Pb.nonneg x.1) (hnn x.2 x.1)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, hsum, mul_one]
    exact Pb.sum_one

/-- **T5(b), a decomposition gives an epistemicization**: for any `λ_θ(ω) ≥ 0` with
`∑_θ λ_θ(ω) = 1`, the extended prior `P⁺(ω, θ) = P̄(ω) λ_θ(ω)` has marginal `P̄` and, at every world
of positive probability, value posterior `P⁺(θ ∣ ω) = λ_θ(ω)` and effective utility
`Ū_a(ω) = ∑_θ λ_θ(ω) u_{θ,a}(ω)`.
Source: [[value-change-as-epistemic-update]] §2.1 ("any `λ_θ(ω) ≥ 0` with `∑_θ λ_θ(ω) = 1` …
gives an epistemicization with `P⁺(θ ∣ ω) = λ_θ(ω)`")
Kind: P
Fidelity: exact
Hyps: (a) `hnn`, `hsum` (the decomposition's own conditions) -/
theorem decomposition_exists (Pb : Prob Ω) (lam : Θ → Ω → ℝ) (u : Θ → A → Ω → ℝ)
    (hnn : ∀ θ ω, 0 ≤ lam θ ω) (hsum : ∀ ω, ∑ θ, lam θ ω = 1) :
    ∃ Pp : Prob (Ω × Θ), (∀ ω, margΩ Pp ω = Pb.p ω) ∧
      ∀ ω, 0 < Pb.p ω → (∀ θ, post Pp θ ω = lam θ ω) ∧ ∀ a, effU Pp u a ω = effUOf lam u a ω := by
  refine ⟨ofDecomp Pb lam hnn hsum, ?_, ?_⟩
  · intro ω
    unfold margΩ ofDecomp
    simp only
    rw [← mul_sum, hsum, mul_one]
  · intro ω hω
    have hm : margΩ (ofDecomp Pb lam hnn hsum) ω = Pb.p ω := by
      unfold margΩ ofDecomp; simp only; rw [← mul_sum, hsum, mul_one]
    have hpost : ∀ θ, post (ofDecomp Pb lam hnn hsum) θ ω = lam θ ω := by
      intro θ
      unfold post
      rw [hm]
      show Pb.p ω * lam θ ω / Pb.p ω = lam θ ω
      field_simp
    refine ⟨hpost, fun a => ?_⟩
    unfold effU effUOf
    simp_rw [hpost]

/-- A posterior family: `Q(θ ∣ ω) ≥ 0`, `∑_θ Q(θ ∣ ω) = 1` for every `ω`.
Source: [[value-change-as-epistemic-update]] §2.2
Kind: D
Fidelity: exact -/
def IsPosterior (Qp : Θ → Ω → ℝ) : Prop := (∀ θ ω, 0 ≤ Qp θ ω) ∧ ∀ ω, ∑ θ, Qp θ ω = 1

/-- **T5(c), reachability is the pointwise convex hull**: a target `Ū'` is the effective utility
of some posterior family `Q(θ ∣ ω)` iff, at every world, the act-vector `(Ū'_a(ω))_a` is a convex
combination of the candidate act-vectors `(u_{θ,a}(ω))_a` — stated with the weights explicit
(a convex combination *is* a nonnegative weighting summing to one), world by world. The two sides
differ only in quantifier order (one family for all `ω` versus weights per `ω`), and that is the
content of the equivalence.
Source: [[value-change-as-epistemic-update]] §2.2 ("Any target in the pointwise convex hull of
the candidates is reachable")
Kind: L (a quantifier exchange, `choose`; audit r1 N3)
Fidelity: exact (hull membership spelled out as explicit weights)
Hyps: (a) none -/
theorem reachable_iff_hull (u : Θ → A → Ω → ℝ) (Ut : A → Ω → ℝ) :
    (∃ Qp : Θ → Ω → ℝ, IsPosterior Qp ∧ ∀ a ω, Ut a ω = effUOf Qp u a ω) ↔
      ∀ ω, ∃ lam : Θ → ℝ, (∀ θ, 0 ≤ lam θ) ∧ ∑ θ, lam θ = 1 ∧ ∀ a, Ut a ω = ∑ θ, lam θ * u θ a ω := by
  constructor
  · rintro ⟨Qp, ⟨hnn, hsum⟩, hU⟩ ω
    exact ⟨fun θ => Qp θ ω, fun θ => hnn θ ω, hsum ω, fun a => hU a ω⟩
  · intro h
    choose lam hnn hsum hU using h
    exact ⟨fun θ ω => lam ω θ, ⟨fun θ ω => hnn ω θ, hsum⟩, fun a ω => hU ω a⟩

/-- The effective utility installed by an outcome `i` of a joint update on `Ω⁺ = Ω × Θ`:
`Ū^{Q_i}_a(ω) = ∑_θ Q_i(θ ∣ ω) u_{θ,a}(ω)` with `Q_i(θ ∣ ω) = Q_i(ω, θ) / Q_i(ω)`.
Source: [[value-change-as-epistemic-update]] §2.2, §3.2 (`Ū^{(i)}_a(ω) := E_{Q_i}[U_a ∣ ω]`)
Kind: D
Fidelity: exact on `Q_i(ω) > 0` -/
def installedEffU {I : Type} [Fintype I] (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (i : I)
    (a : A) (ω : Ω) : ℝ :=
  ∑ θ, (Q.Q i (ω, θ) / ∑ θ', Q.Q i (ω, θ')) * u θ a ω

/-- **T5(d), (Z) is necessary**: under (M) (hence (Z)), an outcome `i` of positive probability
installs, at a world `ω` it gives positive probability, an effective utility that puts weight only
on candidates the prior gives positive weight. So if a target `Ū'` *needs* a zero-prior
candidate — every representation of it as a candidate mixture at `ω` puts positive weight on some
`θ` with `P⁺(ω, θ) = 0` — then no positive-probability outcome of any (M)-update installs it at
`ω`.
Source: [[value-change-as-epistemic-update]] §2.2 ("it may put weight only on candidates the value
prior already gave positive weight to — no update away from zero")
Kind: P
Fidelity: exact
Hyps: (a) `hM : Martingale` (for the joint on `Ω⁺` with outcomes `I`), `0 < π_i`, `0 < Q_i(ω)`;
`hneed` is the hypothesis "the target needs a zero-prior candidate at `ω`" -/
theorem Z_necessary {I : Type} [Fintype I] [DecidableEq I] (J : Joint (Ω × Θ) I)
    (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (Ut : A → Ω → ℝ) (hM : Martingale J Q) (i : I)
    (hi : 0 < J.π i) (ω : Ω) (hQ : 0 < ∑ θ, Q.Q i (ω, θ))
    (hneed : ∀ lam : Θ → ℝ, (∀ θ, 0 ≤ lam θ) → ∑ θ, lam θ = 1 →
      (∀ a, Ut a ω = ∑ θ, lam θ * u θ a ω) → ∃ θ, 0 < lam θ ∧ J.marg (ω, θ) = 0) :
    ∃ a, installedEffU Q u i a ω ≠ Ut a ω := by
  by_contra hall
  push_neg at hall
  have hZ := martingale_imp_noZero hM
  obtain ⟨θ, hθpos, hθzero⟩ := hneed (fun θ => Q.Q i (ω, θ) / ∑ θ', Q.Q i (ω, θ'))
    (fun θ => div_nonneg (Q.nonneg i _) hQ.le)
    (by rw [← sum_div]; exact div_self hQ.ne')
    (fun a => (hall a).symm)
  have := hZ (ω, θ) hθzero i hi
  rw [this, zero_div] at hθpos
  exact lt_irrefl 0 hθpos

/-! ## A witness for `Z_necessary`'s hypothesis package (audit r1, N8) -/

/-- A one-world, two-candidate prior that gives candidate `true` zero weight, with one outcome.
Source: audit r1 (N8)
Kind: D
Fidelity: n/a -/
def zJoint : Joint (Unit × Bool) Unit where
  P := fun x _ => if x.2 then 0 else 1
  nonneg := fun x _ => by split_ifs <;> norm_num
  sum_one := by simp [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The installed state of that outcome: the prior itself.
Source: audit r1 (N8)
Kind: D
Fidelity: n/a -/
def zInstalled : Installed (Unit × Bool) Unit where
  Q := fun _ x => if x.2 then 0 else 1
  nonneg := fun _ x => by split_ifs <;> norm_num
  sum_one := fun _ => by simp [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Candidates `u_true = 1`, `u_false = 0` (one act).
Source: audit r1 (N8)
Kind: D
Fidelity: n/a -/
def zU : Bool → Unit → Unit → ℝ := fun θ _ _ => if θ then 1 else 0

/-- **`Z_necessary`'s package is inhabited**: (M) holds (the one outcome installs the prior),
`π = 1 > 0`, `Q(ω) = 1 > 0`, the target `Ū' = 1` needs the zero-prior candidate `true` (every
mixture representing it puts weight `1` on `true`, where `P⁺ = 0`), and indeed the installed
effective utility is `0 ≠ 1`. Degenerate by design: one world, one act, one outcome, two
candidates, so it exercises exactly the zero-prior-candidate content of `Z_necessary` and nothing
else (audit r2 N4).
Source: [[value-change-as-epistemic-update]] §2.2; audit r1 (N8)
Kind: N− (the theorem is about one world `ω` and one outcome `i` anyway)
Fidelity: exact -/
theorem Z_necessary_package :
    Martingale zJoint zInstalled ∧ 0 < zJoint.π () ∧ 0 < ∑ θ, zInstalled.Q () ((), θ) ∧
    (∀ lam : Bool → ℝ, (∀ θ, 0 ≤ lam θ) → ∑ θ, lam θ = 1 →
      (∀ a : Unit, (fun _ _ => (1 : ℝ)) a () = ∑ θ, lam θ * zU θ a ()) →
      ∃ θ, 0 < lam θ ∧ zJoint.marg ((), θ) = 0) ∧
    ∃ a, installedEffU zInstalled zU () a () ≠ (fun _ _ => (1 : ℝ)) a () := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; rcases x with ⟨_, θ⟩
    cases θ <;> simp [Joint.marg, Joint.π, zJoint, zInstalled, Fintype.sum_prod_type, Fintype.sum_bool]
  · simp [Joint.π, zJoint, Fintype.sum_prod_type, Fintype.sum_bool]
  · simp [zInstalled, Fintype.sum_bool]
  · intro lam _ hsum hrep
    refine ⟨true, ?_, ?_⟩
    · have := hrep ()
      simp [zU, Fintype.sum_bool] at this
      linarith
    · simp [Joint.marg, zJoint]
  · refine ⟨(), ?_⟩
    simp [installedEffU, zInstalled, zU, Fintype.sum_bool]

end

end Cleanroom.Corrigibility.CorrValueChange
