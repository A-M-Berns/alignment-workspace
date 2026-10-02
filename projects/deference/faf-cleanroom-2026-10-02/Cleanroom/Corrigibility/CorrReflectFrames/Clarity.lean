import Cleanroom.Corrigibility.CorrReflectFrames.Compose

/-!
# corr-reflect-frames — T12, T13(a), T16(a): clarity, the generic push, the tautology

* **Corollary I4.1 under clarity** (mm): for an immodest frame, Value ⟺ Total Trust ⟺
  Reflection ⟺ "every positive-cell row is the deferrer's conditional on its own cell" (mm's
  Prop I3.1, the unfolding of `Reflects`). The accuracy leg (DDB Thm 5.1) belongs to
  `lit-ddb-accuracy-mm`, not a dependency, and is omitted (report).
* **No fully reflective agent for a world-independent push** (radical I7.2): with the push
  `K(i | ω) = q i` independent of the world and two targets of positive weight, reflection
  forces both targets to equal the prior.
* **Theorem B under function form is an identity** (joint-adversary A.13.1): the transport of a
  conditional-expectation sign from `π` on `[P = ρ] ∩ L ∩ Pr` to `ρ` on `Pr` is the mechanism
  `reflects_restrict_cell_sum`; `transport_compliance` exhibits the squeeze.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ} {F : Frame W}

/-! ## T12: Corollary I4.1 under clarity -/

/-- **mm Proposition I3.1.** Reflection unfolded: every row at a world of positive cell mass
is the deferrer's conditional on that cell, `π v · 𝟙_{[P = P_w]} v = π(P = P_w) · P_w v` — the
future belief *is* the present belief conditioned on "I will hold exactly these beliefs".
Source: [[mm]] Proposition I3.1 l. 125
Kind: L
Fidelity: exact (product form)
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_iff_rows_cond (hπ : ∀ w, 0 ≤ π w) :
    Reflects π F ↔ ∀ w, 0 < mass π (F.cell (F.P w)) →
      ∀ v, π v * ind (F.cell (F.P w)) v = mass π (F.cell (F.P w)) * F.P w v := by
  constructor
  · intro h w hw v
    exact h (F.P w) ((F.mem_cands_iff_mass_cell_pos hπ).2 hw) v
  · intro h ρ hρ v
    obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
    exact h w (mass_cell_pos_of_pos hπ F hw) v

/-- **Corollary I4.1 (legitimacy under clarity).** For an immodest (clarity-satisfying)
successor frame, the following are equivalent: `π` values it (no fixed-option Dutch book);
Total Trust; Reflection; every positive-cell row is `π`'s conditional on its own cell.
Duplicate of T1 specialised to `Frame.Immodest`; one ledger row. The accuracy leg (DDB Thm 5.1)
is `lit-ddb-accuracy-mm`'s and is omitted here.
Source: [[mm]] Corollary I4.1 l. 140; [[radical]] Theorem I4.1
Kind: C
Fidelity: weaker: the accuracy leg (d) is omitted (owned by `lit-ddb-accuracy-mm`, not a
dependency)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`; clarity (`F.Immodest`) is the scope hypothesis
Scope: immodest frames (mm's clarity) -/
theorem clarity_tfae (hπ : π ∈ stdSimplex ℝ W) (hF : F.Immodest) :
    List.TFAE [Value π F, TotalTrust π F, Reflects π F,
      ∀ w, 0 < mass π (F.cell (F.P w)) →
        ∀ v, π v * ind (F.cell (F.P w)) v = mass π (F.cell (F.P w)) * F.P w v] := by
  have hINT := candsIntrospective_of_immodest hF π
  tfae_have 1 ↔ 2 := value_iff_totalTrust hπ F
  tfae_have 2 ↔ 3 := by
    rw [reflects_iff_totalTrust_and_int hπ.1]
    exact ⟨fun h => ⟨h, hINT⟩, fun h => h.1⟩
  tfae_have 3 ↔ 4 := reflects_iff_rows_cond hπ.1
  tfae_finish

/-! ## T13(a): no fully reflective agent for a world-independent push -/

/-- The joint `P_t(ω, i) = π ω · K(i | ω)` of a prior and a push.
Source: [[radical]] Def I3.2 l. 104, Claim I7.2 l. 199
Kind: D
Fidelity: exact -/
def pushJoint {I : Type} (π : W → ℝ) (K : W → I → ℝ) (w : W) (i : I) : ℝ := π w * K w i

/-- **Reflective for a push and targets**: for every target index of positive weight, the joint's
conditional on `{P_{t+1} = ρ i}` is `ρ i` — `π w · K w i = (∑ w', π w' · K w' i) · ρ i w`.
Source: [[radical]] Claim I7.2 l. 199 ("reflective iff `ρ(ω) = P_t(ω) K(ρ | ω) / P_t(E_ρ)`")
Kind: D
Fidelity: exact (product form) -/
def ReflectiveFor {I : Type} [Fintype I] (π : W → ℝ) (K : W → I → ℝ) (ρ : I → W → ℝ) : Prop :=
  ∀ i, 0 < ∑ w, π w * K w i → ∀ w, π w * K w i = (∑ w', π w' * K w' i) * ρ i w

/-- **I7.2: a world-independent push with two distinct positive-weight targets admits no
reflective prior.** If `K w = q` for all `w` then reflection at `i` reads `π w · q i = q i · ρ i w`,
so `ρ i = π` for every `i` with `q i > 0`; two distinct targets contradict this.
Source: [[radical]] Claim I7.2 l. 199 ("for a generic environment no fully reflective agent
exists"); `s2` (b) (a world-independent push has correction `P`)
Kind: P
Fidelity: weaker: world-independent push only (the source claims "generic `K`"; genericity is
`stretch`, not attempted)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`, `0 < q i`, `0 < q j`, `ρ i ≠ ρ j` -/
theorem no_reflective_of_worldIndependent {I : Type} [Fintype I] (hπ : π ∈ stdSimplex ℝ W)
    {q : I → ℝ} {ρ : I → W → ℝ} {i j : I} (hi : 0 < q i) (hj : 0 < q j) (hne : ρ i ≠ ρ j) :
    ¬ ReflectiveFor π (fun _ => q) ρ := by
  intro h
  have key : ∀ k, 0 < q k → ρ k = π := by
    intro k hk
    funext w
    have hsum : ∑ w', π w' * q k = q k := by rw [← sum_mul, hπ.2, one_mul]
    have := h k (by rw [hsum]; exact hk) w
    rw [hsum] at this
    have e : q k * ρ k w = q k * π w := by linarith
    exact mul_left_cancel₀ hk.ne' e
  exact hne ((key i hi).trans (key j hj).symm)

/-- **N+ instance of I7.2**: `I = Fin 2`, the uniform push `q = (1/2, 1/2)`, targets the two point
masses on `Fin 2` — no reflective prior whatsoever.
Source: [[radical]] Claim I7.2 l. 199; `s2` (b)
Kind: N+
Fidelity: exact
Hyps: (a) none beyond `hπ` -/
theorem no_reflective_uniform_push (π : Fin 2 → ℝ) (hπ : π ∈ stdSimplex ℝ (Fin 2)) :
    ¬ ReflectiveFor π (fun _ => (![1 / 2, 1 / 2] : Fin 2 → ℝ))
      (![![(1 : ℝ), 0], ![0, 1]] : Fin 2 → Fin 2 → ℝ) := by
  apply no_reflective_of_worldIndependent hπ (i := 0) (j := 1) (by norm_num) (by norm_num)
  intro h
  have := congrFun h 0
  norm_num at this

/-! ## T16(a): the transport is an identity under function form -/

/-- **Theorem B under function form is an identity (the squeeze exhibited).** For a deferrer
reflecting `F` conditional on `L`, a candidate `ρ` with `π([P = ρ] ∩ L) > 0`, and any events
`Pr` and variable `X`: `E_π[X | [P = ρ] ∩ L ∩ Pr] ≤ 0 ⟺ E_ρ[X | Pr] ≤ 0` (product forms). The
antecedent "(i⁺) at `S = [P = ρ]`" of joint-adversary A.13.1 *is* the consequent "`ρ` complies
cellwise": the conditional of `π` on `[P = ρ] ∩ L` is `ρ`. Recorded as a finding (kind L,
status `finding`), not a headline.
Source: [[joint-adversary]] A.13.1 l. 107; [[joint]] P.7 l. 211; corr-wf14-2-005
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, Reflection conditional on `L`, positivity of the conditioning cell -/
theorem transport_compliance (hπ : ∀ w, 0 ≤ π w) {L : Finset W}
    (h : Reflects (restrict π L) F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands (restrict π L))
    (hpos : 0 < mass π (F.cell ρ ∩ L)) (Pr : Finset W) (X : W → ℝ) :
    (∑ w ∈ F.cell ρ ∩ L ∩ Pr, π w * X w ≤ 0) ↔ (∑ w ∈ Pr, ρ w * X w ≤ 0) := by
  rw [reflects_restrict_cell_sum hπ h hρ Pr X]
  constructor
  · intro h'
    by_contra hc
    push_neg at hc
    linarith [mul_pos hpos hc]
  · intro h'
    nlinarith

end

end Cleanroom.Corrigibility.CorrReflectFrames
