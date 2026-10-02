import Cleanroom.Found.CorrThreeStep.Identities

/-!
# The general-`A₂` forms

* **T10 (Prop. 9.2)**: the below-threshold inequality on `X` is the sign-split inequality
  `∑_{X > 0} μ·press·X ≤ ∑_{X ≤ 0} μ·press·|X|` — a `sum_filter` split of the product-form
  definition (Kind `L`; the plan's `P` label was for the conditional-form reading, which adds
  only the "multiply by `p(Pr)`" step). The source says "under A1"; the `X`-form needs no A1.
* **T11 (i), (ii)**: for a press-part-maximiser `s` of `Sh`, desideratum 1 is the *conjunction*
  over every continuation `b ∉ Sh` of the below-threshold inequality on `V(b) − V(s)` — "every
  continuation is worse than stopping"; the inequality against one fixed continuation is
  necessary, and sufficient exactly when `Shᶜ` is a singleton. The N+ witness that it is not
  sufficient in general (CE3) is in `Witnesses`.
* **T13 (stretch)**: the value of the button on the full menu equals `max(Δ₋, 0)` when `(c, s)`
  are the press-part-maximisers *and* `c` is also silence- and prior-optimal; plus the
  general-menu facts `0 ≤ VOI` (A1) and `VOI = VOI₂` on a two-option menu.
* **F4(c) on the full menu (repair round 2)**: the source's "`Δ ≤ VOI` in general" is false off
  the two-option menu (finding F-13; the refutation is `Witnesses.s3_voiButton_lt_delta`). What
  Good's argument gives is `E[V(S^H)] − priorMax ≤ VOI`, which under A1 is `≤ Δ`; `Δ ≤ VOI` holds
  when `s` is prior-optimal within `Sh` (in particular when `Sh = {s}`, or on `{c, s}`).

Sources: `miri.md` Prop. 9.2; `general-object-final.md` S2, S6(b); `christiano.md` C4;
`byrnes-herd.md` Claim 2.4; `filler.md` F4(c).
-/

namespace Cleanroom.Found.CorrThreeStep

namespace ThreeStep

open FactoredSpaces Finset

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-! ## T10 — Prop. 9.2: the sensor condition on a general finite `Ω` -/

/-- **Prop. 9.2 (sensor condition for D1), product form.** With `Ω⁺ = {ω | 0 < X ω}` and
`Ω⁻ = {ω | X ω ≤ 0}`: the below-threshold inequality on `X` at `a₁` holds iff
`∑_{Ω⁺} μ(ω) P(Pr|ω) X(ω) ≤ ∑_{Ω⁻} μ(ω) P(Pr|ω) |X(ω)|`. A split of the defining sum by the sign
of `X`; the source's "under A1" is not needed in this `X`-form (A1 only matters for building
`X` from `V`).
Source: [[corr-wf13-inventory]] 011 / miri.md Prop. 9.2
Kind: L
Fidelity: exact (on the product-form definition; the conditional-form reading adds the
`0 < pressMass` step of `belowThresholdIneq_iff_condExpPress`)
Hyps: (a) only -/
theorem belowThresholdIneq_iff_sign_split (a : A₁) (X : Ω → ℝ) :
    S.belowThresholdIneq a X ↔
      ∑ ω ∈ univ.filter (fun ω => 0 < X ω), (S.μ a).mass ω * S.press a ω * X ω ≤
        ∑ ω ∈ univ.filter (fun ω => X ω ≤ 0), (S.μ a).mass ω * S.press a ω * |X ω| := by
  unfold belowThresholdIneq obsExpect
  simp only [obsWeight_press]
  rw [← sum_filter_add_sum_filter_not univ (fun ω => 0 < X ω)]
  have hfilt : univ.filter (fun ω => ¬ 0 < X ω) = univ.filter (fun ω => X ω ≤ 0) :=
    filter_congr fun ω _ => not_lt
  rw [hfilt]
  have hneg : ∑ ω ∈ univ.filter (fun ω => X ω ≤ 0), (S.μ a).mass ω * S.press a ω * X ω =
      -∑ ω ∈ univ.filter (fun ω => X ω ≤ 0), (S.μ a).mass ω * S.press a ω * |X ω| := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun ω hω => ?_
    rw [mem_filter] at hω
    rw [abs_of_nonpos hω.2]
    ring
  rw [hneg]
  constructor <;> intro h <;> linarith

/-! ## T11 — the general-`A₂` form of desideratum 1 -/

/-- **T11(i).** For a press-part-maximiser `s` of `Sh`: desideratum 1 at `a₁` iff for *every*
continuation `b ∉ Sh` the below-threshold inequality holds on `V(b) − V(s)` — the press reads
"every continuation is worse than stopping".
Source: [[corr-wf14b-inventory]] 004 / general-object-final.md S2(a), S6(b); [[corr-wf13-2-inventory]] 071
Kind: L
Fidelity: stronger: any `Sh` with `s` a press-part-maximiser of it (S2(a)/S6(b) state it with `Sh = {a_∅}`)
Hyps: (a) `hs` is the part-maximiser predicate of record -/
theorem d1At_iff_forall_cont (a : A₁) {s : A₂} (hs : S.IsPartBest a .press S.Sh s) :
    S.D1At a ↔ ∀ b ∉ S.Sh, S.belowThresholdIneq a (S.Xo a .press b s) := by
  unfold D1At belowThresholdIneq
  constructor
  · rintro ⟨b₀, hb₀, hopt⟩ b _
    rw [S.obsExpect_Xo, sub_nonpos]
    exact (hopt b).trans (hs.2 b₀ hb₀)
  · intro h
    refine ⟨s, hs.1, fun b' => ?_⟩
    by_cases hb' : b' ∈ S.Sh
    · exact hs.2 b' hb'
    · have := h b' hb'
      rw [S.obsExpect_Xo, sub_nonpos] at this
      exact this

/-- **T11(ii), necessity.** Desideratum 1 implies the below-threshold inequality against any one
fixed continuation `b ∉ Sh` (with `s` a press-part-maximiser of `Sh`).
Source: [[corr-wf14b-inventory]] 004 / general-object-final.md S2(c) ("necessary")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem belowThresholdIneq_of_d1At (a : A₁) {s : A₂} (hs : S.IsPartBest a .press S.Sh s)
    (hd1 : S.D1At a) {b : A₂} (hb : b ∉ S.Sh) : S.belowThresholdIneq a (S.Xo a .press b s) :=
  (S.d1At_iff_forall_cont a hs).mp hd1 b hb

/-- **T11(ii), sufficiency on a singleton menu.** When `Shᶜ = {c}` the single inequality against
`c` gives desideratum 1. (Its failure with two continuations is `Witnesses.ce3`.)
Source: [[corr-wf14b-inventory]] 004 / general-object-final.md S2(c) ("sufficient iff `|A| = 2`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1At_of_singleton_cont (a : A₁) {c s : A₂} (hs : S.IsPartBest a .press S.Sh s)
    (hcont : S.Shᶜ = {c}) (h : S.belowThresholdIneq a (S.Xo a .press c s)) : S.D1At a := by
  rw [S.d1At_iff_forall_cont a hs]
  intro b hb
  have : b ∈ S.Shᶜ := mem_compl.mpr hb
  rw [hcont, mem_singleton] at this
  subst this
  exact h

/-! ## T13 — the value of the button on the full menu -/

/-- The `o`-weighted max over `A₂` is the max over a part-maximiser pair.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_eq_of_partBest (a : A₁) (o : Obs) {c s : A₂} (hc : S.IsPartBest a o S.Shᶜ c)
    (hs : S.IsPartBest a o S.Sh s) :
    S.obsMax a o = max (S.obsExpect a o (S.V a o c)) (S.obsExpect a o (S.V a o s)) := by
  unfold obsMax
  apply le_antisymm
  · rw [sup'_le_iff]
    intro b _
    by_cases hb : b ∈ S.Sh
    · exact (hs.2 b hb).trans (le_max_right _ _)
    · exact (hc.2 b (mem_compl.mpr hb)).trans (le_max_left _ _)
  · exact max_le (le_sup' (fun b => S.obsExpect a o (S.V a o b)) (mem_univ c))
      (le_sup' (fun b => S.obsExpect a o (S.V a o b)) (mem_univ s))

/-- The `o`-weighted max over `A₂` is attained by an `o`-optimal action.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_eq_of_optimal (a : A₁) (o : Obs) {c : A₂}
    (hc : ∀ b, S.obsExpect a o (S.V a o b) ≤ S.obsExpect a o (S.V a o c)) :
    S.obsMax a o = S.obsExpect a o (S.V a o c) := by
  unfold obsMax
  exact le_antisymm ((sup'_le_iff S.univ_nonempty _).mpr fun b _ => hc b)
    (le_sup' (fun b => S.obsExpect a o (S.V a o b)) (mem_univ c))

/-- The prior max over `A₂` is attained by a prior-optimal action.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma priorMax_eq_of_optimal (a : A₁) (o₀ : Obs) {c : A₂}
    (hc : ∀ b, S.priorValue a o₀ b ≤ S.priorValue a o₀ c) : S.priorMax a o₀ = S.priorValue a o₀ c := by
  unfold priorMax
  exact le_antisymm ((sup'_le_iff S.univ_nonempty _).mpr fun b _ => hc b)
    (le_sup' (fun b => S.priorValue a o₀ b) (mem_univ c))

/-- `max x 0 − x = max (−x) 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma max_zero_sub_self (x : ℝ) : max x 0 - x = max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **T13.** On the full menu `A₂`, the value of the button is `max(Δ₋, 0)` when `(c, s)` are the
press-part-maximisers of `Shᶜ` and `Sh` *and* `c` is also silence-optimal and prior-optimal over
all of `A₂` (the general-menu version of the continue-by-default regime). Where those extra
hypotheses fail the identity can fail: in CE3 the press-part-maximiser of `Shᶜ` is `p2`, which is
neither silence- nor prior-optimal, and `voiButton = 9/5 ≠ max(Δ₋(p2, null), 0) = 0`
(`Witnesses.ce3_voiButton_ne_max`). The full package is inhabited on a four-action menu with
`Δ₋ = 2/5 > 0` (`Witnesses.w13_voiButton`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (stated there on a two-option menu)
Kind: L (three max-identifications by the named optimality hypotheses; relabelled from P in repair round 1)
Fidelity: variant: general `A₂` with the named optimality hypotheses on `c`
Hyps: (a) A1 as Dict-5; (a) `hc`, `hs`, `hcs`, `hcp` name the regime on the full menu -/
theorem voiButton_eq_max_deltaMinus (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s)
    (hcs : ∀ b, S.obsExpect a .silent (S.V a .silent b) ≤ S.obsExpect a .silent (S.V a .silent c))
    (hcp : ∀ b, S.priorValue a o₀ b ≤ S.priorValue a o₀ c) :
    S.voiButton a o₀ = max (S.deltaMinus a c s) 0 := by
  unfold voiButton
  rw [S.obsMax_eq_of_partBest a .press hc hs, S.obsMax_eq_of_optimal a .silent hcs,
    S.priorMax_eq_of_optimal a o₀ hcp, S.priorValue_eq_of_A1 hA1 a o₀ c,
    max_eq_add_max_sub (S.obsExpect a .press (S.V a .press c))]
  have hm : S.deltaMinus a c s =
      -(S.obsExpect a .press (S.V a .press c) - S.obsExpect a .press (S.V a .press s)) := by
    rw [deltaMinus, S.obsExpect_Xo]
  rw [hm, ← max_zero_sub_self]
  ring

/-- **The value of the button is nonnegative on the full menu** (A1): the informed agent may play
the prior-best action whatever it observes. (`miri.md` Prop. 10.5's strict-positivity *iff* is
not formalized; only its `≥ 0` half is this theorem.)
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c), second half
Kind: L
Fidelity: exact
Hyps: (a) A1 as Dict-5 -/
theorem voiButton_nonneg (hA1 : S.A1) (a : A₁) (o₀ : Obs) : 0 ≤ S.voiButton a o₀ := by
  unfold voiButton
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' S.univ_nonempty (fun b => S.priorValue a o₀ b)
  unfold priorMax
  rw [hb, S.priorValue_eq_of_A1 hA1 a o₀ b]
  have h1 : S.obsExpect a .press (S.V a .press b) ≤ S.obsMax a .press :=
    le_sup' (fun b => S.obsExpect a .press (S.V a .press b)) (mem_univ b)
  have h2 : S.obsExpect a .silent (S.V a .silent b) ≤ S.obsMax a .silent :=
    le_sup' (fun b => S.obsExpect a .silent (S.V a .silent b)) (mem_univ b)
  linarith

/-- On a two-option menu (`∀ b, b = c ∨ b = s`) the full-menu value of the button is the
two-option one.
Source: [[corr-wf14-inventory]] 005 / filler.md F4 (the two-option menu)
Kind: L
Fidelity: exact -/
theorem voiButton_eq_voiButton2 (a : A₁) (o₀ : Obs) {c s : A₂} (hmenu : ∀ b : A₂, b = c ∨ b = s) :
    S.voiButton a o₀ = S.voiButton2 a o₀ c s := by
  have key : ∀ f : A₂ → ℝ, univ.sup' S.univ_nonempty f = max (f c) (f s) := fun f =>
    le_antisymm
      ((sup'_le_iff S.univ_nonempty f).mpr fun b _ => by
        rcases hmenu b with rfl | rfl
        · exact le_max_left _ _
        · exact le_max_right _ _)
      (max_le (le_sup' f (mem_univ c)) (le_sup' f (mem_univ s)))
  unfold voiButton voiButton2 obsMax priorMax twoOptionValue twoOptionPriorValue
  rw [key, key, key]

/-! ## F4(c) on the full menu (repair round 2)

`filler.md` F4(c) claims `Δ ≤ VOI` "in general (no regime assumption)" with `VOI` the full-menu
value of the button, by "letting the button decide is one strategy the informed agent may use".
On the full menu the claim is **false** (`Witnesses.s3_voiButton_lt_delta`: three actions,
`Sh = {s, b}`, `VOI = 1/2 < 1 = Δ` with A1, a press-part-maximiser pair, the two-option regime
and D1 all in force; finding F-13). What the argument does give is the lower bound
`E[V(S^H)] − priorMax ≤ VOI`, which under A1 sits *below* `Δ`; `Δ ≤ VOI` holds exactly where the
prior-best shutdown action is `s` itself. -/

/-- **Good's theorem's finite core, full menu.** Letting the button decide (`S^H`) is one
strategy the informed agent may use, so `E[V(S^H)] − priorMax ≤ VOI`. No A1 needed. This — not
`Δ ≤ VOI` — is what filler F4(c)'s argument proves on the full menu; under A1 the left side is
`≤ Δ` (`shPolicy_sub_priorMax_le_delta`), so the argument cannot deliver `Δ ≤ VOI`, and
`Witnesses.s3_voiButton_lt_delta` shows nothing else does either.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (the argument, not the claim)
Kind: L
Fidelity: weaker: the lower bound the argument gives; the claim `Δ ≤ VOI` is false on the full menu (finding F-13)
Hyps: (a) only -/
theorem shPolicy_sub_priorMax_le_voiButton (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.jointExpect a (S.shPolicy a c s) - S.priorMax a o₀ ≤ S.voiButton a o₀ := by
  rw [jointExpect_eq, shPolicy_press, shPolicy_silent]
  unfold voiButton
  have h1 : S.obsExpect a .press (S.V a .press s) ≤ S.obsMax a .press :=
    le_sup' (fun b => S.obsExpect a .press (S.V a .press b)) (mem_univ s)
  have h2 : S.obsExpect a .silent (S.V a .silent c) ≤ S.obsMax a .silent :=
    le_sup' (fun b => S.obsExpect a .silent (S.V a .silent b)) (mem_univ c)
  linarith

/-- **Good's lower bound sits below `Δ`** (A1): `E[V(S^H)] − priorMax ≤ Δ`, because the full-menu
prior maximum dominates both two-option constants. On a two-option menu the two coincide, which
is why `delta_le_voiButton2` holds there.
Source: none: derived here (why filler F4(c)'s argument stops short on the full menu)
Kind: L
Fidelity: n/a
Hyps: (a) A1 as Dict-5 -/
theorem shPolicy_sub_priorMax_le_delta (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.jointExpect a (S.shPolicy a c s) - S.priorMax a o₀ ≤ S.delta a c s := by
  have hc : S.priorValue a o₀ c ≤ S.priorMax a o₀ :=
    le_sup' (fun b => S.priorValue a o₀ b) (mem_univ c)
  have hs : S.priorValue a o₀ s ≤ S.priorMax a o₀ :=
    le_sup' (fun b => S.priorValue a o₀ b) (mem_univ s)
  have e1 := S.jointExpect_shPolicy_sub_cont a c s
  have e2 := S.jointExpect_shPolicy_sub_stop a c s
  have pc : S.jointExpect a (S.constPolicy a c) = S.priorValue a o₀ c := by
    rw [jointExpect_eq, constPolicy_apply, constPolicy_apply, S.priorValue_eq_of_A1 hA1]
  have ps : S.jointExpect a (S.constPolicy a s) = S.priorValue a o₀ s := by
    rw [jointExpect_eq, constPolicy_apply, constPolicy_apply, S.priorValue_eq_of_A1 hA1]
  rw [pc] at e1
  rw [ps] at e2
  unfold delta
  exact le_min (by linarith) (by linarith)

/-- **The corrected F4(c) on the full menu.** `Δ ≤ VOI` holds whenever `c` is a press-part-
maximiser of `Shᶜ` and `s` is *prior-optimal within `Sh`* (any number of continuations, any
number of shutdown actions): the prior-best action of the whole menu is either a continuation —
then the informed agent, playing `s` on a press and that action on silence, gains at least `Δ₋` —
or a shutdown action no better on the prior than `s` — then playing `c` on silence and `s` on a
press gains at least `Δ₊`. `Witnesses.s3_voiButton_lt_delta` shows the hypothesis on `s` cannot
be dropped (there a shutdown action `b ≠ s` is prior-best). `hs` (press-optimality of `s`) is not
needed.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (corrected: the claim as stated is false on the full menu, finding F-13)
Kind: L
Fidelity: variant: needs `s` prior-optimal within `Sh` (automatic on `{c, s}` and whenever `Sh = {s}`)
Hyps: (a) A1 as Dict-5; (a) `hc` the part-maximiser predicate of record; (a) `hsp` names the prior-optimality of `s` within `Sh` -/
theorem delta_le_voiButton_of_prior_best_sh (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c)
    (hsp : ∀ b ∈ S.Sh, S.priorValue a o₀ b ≤ S.priorValue a o₀ s) :
    S.delta a c s ≤ S.voiButton a o₀ := by
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' S.univ_nonempty (fun b => S.priorValue a o₀ b)
  have hbeq : S.priorMax a o₀ = S.priorValue a o₀ b := hb
  have hsmax : S.priorValue a o₀ s ≤ S.priorMax a o₀ :=
    le_sup' (fun b => S.priorValue a o₀ b) (mem_univ s)
  have hPs : S.obsExpect a .press (S.V a .press s) ≤ S.obsMax a .press :=
    le_sup' (fun b => S.obsExpect a .press (S.V a .press b)) (mem_univ s)
  have hSc : S.obsExpect a .silent (S.V a .silent c) ≤ S.obsMax a .silent :=
    le_sup' (fun b => S.obsExpect a .silent (S.V a .silent b)) (mem_univ c)
  have hSb : S.obsExpect a .silent (S.V a .silent b) ≤ S.obsMax a .silent :=
    le_sup' (fun b => S.obsExpect a .silent (S.V a .silent b)) (mem_univ b)
  have hm : S.deltaMinus a c s =
      S.obsExpect a .press (S.V a .press s) - S.obsExpect a .press (S.V a .press c) := by
    rw [deltaMinus, S.obsExpect_Xo]; ring
  have hp : S.deltaPlus a c s =
      S.obsExpect a .silent (S.V a .silent c) - S.obsExpect a .silent (S.V a .silent s) := by
    rw [deltaPlus, S.obsExpect_Xo]
  unfold voiButton delta
  by_cases hbSh : b ∈ S.Sh
  · have hbs : S.priorValue a o₀ b = S.priorValue a o₀ s :=
      le_antisymm (hsp b hbSh) (hsmax.trans_eq hbeq)
    rw [hbeq, hbs, S.priorValue_eq_of_A1 hA1 a o₀ s]
    exact (min_le_right _ _).trans (by linarith)
  · have := hc.2 b (mem_compl.mpr hbSh)
    rw [hbeq, S.priorValue_eq_of_A1 hA1 a o₀ b]
    exact (min_le_left _ _).trans (by linarith)

/-- **F4(c) on the full menu with a single shutdown action.** When `Sh = {s}` (any number of
continuations), `Δ ≤ VOI` for every press-part-maximiser `c` of `Shᶜ` — the case of
`delta_le_voiButton_of_prior_best_sh` where the prior-optimality of `s` within `Sh` is trivial.
The symmetric twin of T11(ii): the single-pair statement is right when the *other* part is a
singleton.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (corrected; finding F-13)
Kind: L
Fidelity: variant: needs `Sh = {s}`
Hyps: (a) A1 as Dict-5; (a) `hc` the part-maximiser predicate of record -/
theorem delta_le_voiButton_of_singleton_sh (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hSh : S.Sh = {s}) :
    S.delta a c s ≤ S.voiButton a o₀ :=
  S.delta_le_voiButton_of_prior_best_sh hA1 a o₀ hc fun b hb => by
    rw [hSh, mem_singleton] at hb
    rw [hb]

/-- **F4(c) on a two-option menu**: `Δ ≤ VOI` when every action is `c` or `s` — the case the
source's `[checked]` runs presumably exercised.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c)
Kind: L
Fidelity: exact on the two-option menu
Hyps: (a) A1 as Dict-5; (a) `hmenu` names the two-option menu -/
theorem delta_le_voiButton_of_two_option (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hmenu : ∀ b : A₂, b = c ∨ b = s) : S.delta a c s ≤ S.voiButton a o₀ := by
  rw [S.voiButton_eq_voiButton2 a o₀ hmenu]
  exact S.delta_le_voiButton2 hA1 a o₀ c s

end ThreeStep

end Cleanroom.Found.CorrThreeStep
