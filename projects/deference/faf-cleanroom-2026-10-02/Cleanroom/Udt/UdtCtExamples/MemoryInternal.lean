import Cleanroom.Udt.UdtCommTrust.SelfTrust
import Cleanroom.Udt.UdtCtExamples.MemoryHidden

/-!
# `Cleanroom.Udt.UdtCtExamples.MemoryInternal`: the Memory Problem with the pill as a realized
internal action (T2, repair round 2)

Work package `udt-ct-examples`, target T2 — the mandate's own fallback ("try the design where
the light-instance internal action is the only route, and report either way"), asked for by
audit r1 adversarial B1 (iii) and audit r2 fidelity N2. Source: [[communication-trust-translated]]
lines 159–166 and 176–178 (internal actions "such as recalling or storing memories"), the C&T
LaTeX draft's "merely some probabilistic relationship between internal actions and (potentially
self-modifying) internal observations"; [[examples-revisited]] Example 2.

## Why a third Memory carrier

`Mem` makes the pill choice the light instance's *external* action (so `Π̈(light)` reveals it:
decision-determination holds through the leak, and the CA failure is the leak); `MemH` hides
the choice from `Π̈` by making it no action at all (so decision-determination fails, but
`MinMod`/`IsCA` cannot be asked of the pill). `MemI` is the paper's picture proper: the pill is
a **realized internal action** `c'` of the light instance (`AI = Fin 2`, `Ȧ(light) = c'`), the
pill content `d : Fin 3` a coordinate of `D_I` support-independent of `c'` (as `I_fac` demands)
and tied to it in law — `CBm`-style, `6 : 1 : 1` without the pill (`d = none, red, green`) and
`2 : 3 : 3` with it, so the pill "takes" with probability `3/4` and "nothing" is modifying with
probability `1/4` — and the light instance's external action the dummy `r` (the unforced report,
as in `MemH`). `Π̈ = (light ↦ r, asked ↦ report(d, r))` hides `c'`; `Π*(light input) = (c', r)`
carries it, so the pill is an action the Self-Trust theorem's notions apply to.

Worlds `(((c', d), r), (ö, ℓ))`, 48 of them. Weights: `tie c' d` times `4` at a light world,
times `4` at an asked world without a pill (the unforced report is uncorrelated with the light —
the memory wipe) and `7 : 1` towards the pill's colour with one (the pill works). Total `512`.

## What holds on this carrier

* **Decision-determination fails** (`not_decisionDetermined`), by the `MemH` mechanism: clause
  (1) holds (`U_sub_E`) and clause (2) fails at `e = (report red, (asked, light red))`,
  `d = (red pill, (pill, r = red))`, where the count identity reads `21 · 192 = 60 · 48`
  (`key_values`): given the report "red", the light is red with probability `7/8` after a pill and
  `1/2` without one, and `Π̈` cannot tell.
* **The pill has no communicative alternative** (`not_isCA_pill`, `not_hasCA`) **for the paper's
  reason**: the only minimally modifying actions are the "nothing" actions (`minMod_nothing`,
  `not_minMod_pill`; `m(pill) = 3/4`, `m(nothing) = 1/4`), and the law of `Π̈` given `(pill, r)`
  differs from the law given `(nothing, r)` **at the report coordinate** (`report_law_differs`:
  `P(report = r ∣ pill, r) = 5/8` against `7/8`) — the pill decouples the report from the unforced
  report policy. Contrast `Mem.asked_law_agrees`, where the separation was only at the
  representation's leaking coordinate.
* **The pill is strictly preferred** at every light input (`score_light`: `19/64 < 25/64`), so
  the repaired Self-Trust conclusion fails there (`not_minMod_argmax`) — as it must, since both
  of the theorem's substantive hypotheses fail.

So on the paper's own internal-action picture the Memory Problem fails **both**
decision-determination and communicative alternatives (findings F-15, repair round 2): the
retracted "DD fails" and the corrected "CA fails" are both right, each on the coordinate it is
about, and neither is a representation artifact here.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace MemI

/-- Worlds `(((c', d), r), (ö, ℓ))`: `c'` the internal pill action (`0` nothing, `1` pill), `d`
the pill content (`0` none, `1` red, `2` green), `r` the unforced report policy, `ö` the focal
instance (`0` light, `1` asked), `ℓ` the light.
Source: none: infrastructure (mandate T2, the sketch's internal pill; repair round 2)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := ((Fin 2 × Fin 3) × Fin 2) × (Fin 2 × Fin 2)

/-- The external observation: the light at the light instance, `2` at the asked instance.
Source: [[communication-trust-translated]] line 160
Kind: D
Fidelity: exact
Hyps: n/a -/
def obs (ω : Ω) : Fin 3 := if ω.2.1 = 0 then Fin.castSucc ω.2.2 else 2

/-- The utility numerator: `1` iff the focal instance is asked and the report (`MemH.actOf`: forced
by the pill, else `r`) equals the light.
Source: [[communication-trust-translated]] line 160 ("rewarded for a correct answer")
Kind: D
Fidelity: exact
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 1 ∧ MemH.actOf ω.1.1.2 ω.1.2 (obs ω) = ω.2.2 then 1 else 0

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 1 := by revert ω; decide

/-- The chosen policy of dynamics `(c', r)`: `(c', r)` at a light input — the internal pill
action and the dummy external action — and `(0, r)` at the asked input.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (c' : Fin 2) (r : Fin 2) (oe : Fin 3 × Fin 3) : Fin 2 × Fin 2 :=
  if oe.2 = 2 then (0, r) else (c', r)

/-- The tie between the pill action and the pill content: `6 : 1 : 1` without the pill,
`2 : 3 : 3` with it (the pill takes with probability `3/4`; "nothing" is modifying with
probability `1/4`). Every pair has positive weight, as `I_fac` requires.
Source: mandate T1(d) (the `CBm` picture), T2 (the fallback design)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def tie (c' : Fin 2) (d : Fin 3) : ℕ :=
  if c' = 0 then (if d = 0 then 6 else 1) else (if d = 0 then 2 else 3)

/-- The weights (module docstring): `tie c' d` times `4` at a light world, times `4` at an asked
world without a pill, times `7 : 1` towards the pill's colour with one. Total `512`.
Source: mandate T2 (the prior)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := tie ω.1.1.1 ω.1.1.2 * (if ω.2.1 = 0 then 4 else if ω.1.1.2 = 0 then 4 else
    (if (if ω.1.1.2 = 1 then (0 : Fin 2) else 1) = ω.2.2 then 7 else 1))
  pos ω := by revert ω; decide
  N := 512
  sum_eq := by decide +kernel

/-- **The Memory Problem with the pill as a realized internal action, abstract structure.**
Source: [[communication-trust-translated]] lines 159–166, 176–178; mandate T2 (the fallback design); audit r2 fidelity N2
Kind: N+
Fidelity: variant: the pill a realized internal action `Ȧ(light) = c'` with a probabilistic effect (`3/4`) on the content `d ∈ D_I`; `Ä(light)` the dummy `r`; the colour not chosen (as `Mem`); light and content correlated in law only; §3 (c)
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 3) (Fin 3) (Fin 2) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) (Fin 1) (Fin 3) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1.1.2
  oE := obs
  aI ω := if ω.2.1 = 0 then ω.1.1.1 else 0
  aE ω := MemH.actOf ω.1.1.2 ω.1.2 (obs ω)
  dI ω := ω.1.1.2
  dE ω := ω.2
  dB ω := (ω.1.1.1, ω.1.2)
  oH _ := 0
  oC ω := ω.1.1.2
  polS ω := polOf' ω.1.1.1 ω.1.2
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) u_le
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((if ω₁.2.1 = 0 then ω₁.1.1.1 else 0, ω₂.1.1.2), ω₁.1.2), (0, 0)))
    (by decide +kernel)
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((0, 0), MemH.actOf ω₁.1.1.2 ω₁.1.2 (obs ω₁)), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => (((ω₂.1.1.1, ω₁.1.1.2), ω₂.1.2), ω₁.2))
    (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((if ω₁.2.1 = 0 then ω₁.1.1.1 else 0, 0),
      MemH.actOf ω₂.1.1.2 ω₂.1.2 (obs ω₂)), (0, 0))) (by decide +kernel)

/-- **The Memory Problem with the pill as a realized internal action, concrete structure**: no
messages; the pills force the report (`Mem.pfun`).
Source: [[communication-trust-translated]] lines 159–166; mandate T2
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 3) (Fin 3) (Fin 2) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) (Fin 1) (Fin 3) where
  toAbstractDS := absDS
  s _ _ := none
  p := Mem.pfun

/-! ### Reading `Π̈`, `Π*`, the modification event off the coordinates -/

/-- **`Π̈` on `MemI`**: `(light ↦ r, asked ↦ report(d, r))` — the pill action `c'` is hidden.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun e => MemH.actOf ω.1.1.2 ω.1.2 e :=
  S.polE_eq_of (fun ω e => MemH.actOf ω.1.1.2 ω.1.2 e) (fun _ => rfl) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 3 × (Fin 2 × Fin 2)) : S.polOf d = fun e => MemH.actOf d.1 d.2.2 e := by
  obtain ⟨d1, c, r⟩ := d
  exact polE_eq (((c, d1), r), (0, 0))

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 3 → Fin 2) :
    S.evPolE π = event fun ω : Ω => (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- **`Π̈` hides the pill action**: worlds with the same content and report policy have the same
external policy whatever `c'` is.
Source: mandate T2 (the sketch's internal pill)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_hides_pill (ω ω' : Ω) (hd : ω.1.1.2 = ω'.1.1.2) (hr : ω.1.2 = ω'.1.2) :
    S.polE ω = S.polE ω' := by
  rw [polE_eq, polE_eq, hd, hr]

/-- Supporting lemma `evS_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (o : Fin 3) (e : Fin 3) (a : Fin 2 × Fin 2) :
    S.evS o e a = event fun ω : Ω => polOf' ω.1.1.1 ω.1.2 (o, e) = a := rfl

/-- **`Π* ⊑ D_{I,B}` on `MemI`.**
Source: mandate T2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem polS_sub : IsSubvariable S.DIB S.polS := by
  show ∀ ω ω' : Ω, (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (ω'.1.1.2, (ω'.1.1.1, ω'.1.2)) →
    polOf' ω.1.1.1 ω.1.2 = polOf' ω'.1.1.1 ω'.1.2
  decide +kernel

/-- **`R ⊑ D_{I,B}` on `MemI`** (silent everywhere, `rfl` — degenerate).
Source: mandate T2
Kind: N−
Fidelity: n/a (vacuous: `R` is constant)
Hyps: none -/
theorem R_sub_DIB : IsSubvariable S.DIB S.R := fun _ _ _ => rfl

/-- **`P(Π̈ = R) = 1` on `MemI`**, vacuously (no message channel).
Source: mandate T2
Kind: N−
Fidelity: n/a (vacuous)
Hyps: none -/
theorem followsR : mass S.μ.w S.evFollowsR = 1 := by
  have : S.evFollowsR = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rw [ConcreteDS.mem_evFollowsR]
    intro e a h
    exact absurd h (by simp [ConcreteDS.R, S])
  rw [this]
  exact mass_univ S.μ

/-- Supporting lemma `evMod_eq`: the modified worlds are those with a pill content.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : S.evMod = event fun ω : Ω => ω.1.1.2 ≠ 0 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 3, (Mem.pfun e ω.1.1.2).isSome) ↔ ω.1.1.2 ≠ 0
  revert ω
  decide +kernel

/-- Supporting lemma: at a light input every action `(c', r)` is attained.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_light_nonempty (o e : Fin 3) (he : e ≠ 2) (a : Fin 2 × Fin 2) :
    (S.evS o e a).Nonempty := by
  rw [evS_eq]; revert o e a; decide +kernel

/-- **The prose meaning of `Π*` holds on `MemI`** (`hlink`): at every unforced realized input the
effective action is the chosen one — including the internal pill action at the light instance.
Source: mandate T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω) := by
  intro ω h
  have h' : Mem.pfun (obs ω) ω.1.1.2 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((if ω.2.1 = 0 then ω.1.1.1 else 0), MemH.actOf ω.1.1.2 ω.1.2 (obs ω)) =
    polOf' ω.1.1.1 ω.1.2 (ω.1.1.2, obs ω)
  revert ω
  decide +kernel

/-! ### Decision-determination fails, by the `MemH` mechanism -/

/-- Supporting lemma: `U` is a function of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω,
    (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (MemH.actOf ω'.1.1.2 ω'.1.2 (obs ω'), ω'.2) →
    u ω = u ω' := by decide +kernel

/-- **Clause (1) of decision-determination holds on `MemI`**: `U ⊑ E`.
Source: [[examples-revisited]] Example 2 (corrected); mandate T2(a)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem U_sub_E : IsSubvariable S.E S.U := by
  intro ω ω' h
  show natDiv u 1 ω = natDiv u 1 ω'
  unfold natDiv
  rw [u_of_E ω ω' h]

/-- Supporting lemma: the four counts of the failing atom, in weight units (total `512`):
`P(E = e, D_{I,B} = d) = 21`, `P(Π̈ = [[d]]) = 192`, `P(E = e, Π̈ = [[d]]) = 60`,
`P(D_{I,B} = d) = 48` at `e = (report red, (asked, light red))`, `d = (red pill, (pill, r = red))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key_values :
    weights.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (0, (1, 0)) ∧
        (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, 0))) = 21 ∧
    weights.cnt (event fun ω : Ω =>
        (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun e => MemH.actOf 1 0 e) = 192 ∧
    weights.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun e => MemH.actOf 1 0 e) = 60 ∧
    weights.cnt (event fun ω : Ω => (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, 0))) = 48 := by
  decide +kernel

/-- Supporting lemma: the failing atom as a count inequality (`21 · 192 ≠ 60 · 48`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key :
    weights.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (0, (1, 0)) ∧
        (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, 0))) *
      weights.cnt (event fun ω : Ω =>
        (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun e => MemH.actOf 1 0 e) ≠
    weights.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun e => MemH.actOf 1 0 e) *
      weights.cnt (event fun ω : Ω => (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, 0))) := by
  decide +kernel

/-- **With the pill a realized internal action, the Memory Problem is not decision-determined**:
clause (2) fails at `e = (report red, (asked, light red))`, `d = (red pill, (pill, r = red))`,
where the division-free identity reads `21 · 192 = 60 · 48` (`key_values`) — the `MemH`
mechanism: given the report "red", the light is red with probability `7/8` after a pill and
`1/2` without one, while `Π̈ = (red, red, red)` either way. The diagnosis
[[examples-revisited]] retracted holds on the paper's own picture of the pill (findings F-15).
Source: [[examples-revisited]] Example 2 (the retracted diagnosis); [[communication-trust-translated]] lines 159–166, 176–178, 381–390; mandate T2(a) ("record the atom")
Kind: N+
Fidelity: exact (on this representation; the atom is named)
Hyps: none; §3 (c) -/
theorem not_decisionDetermined : ¬ S.DecisionDetermined := fun h => by
  have := h.2 (0, (1, 0)) (1, (1, 0))
  have hev : (event fun ω => S.E ω = (0, (1, 0)) ∧ S.polE ω = S.polOf (1, (1, 0))) =
      event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2 (obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun e => MemH.actOf 1 0 e :=
    event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
  rw [hev, evPolE_eq, polOf_eq] at this
  apply key
  have := congrArg (fun x => x * (weights.N : ℝ) * weights.N) this
  simp only [show S.μ.w = weights.w from rfl, weights.mass_eq_cnt] at this
  have hN : (weights.N : ℝ) ≠ 0 := by exact_mod_cast weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

/-! ### Modification: the pill `3/4`, "nothing" `1/4` -/

/-- Supporting lemma `modS_le_of_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem modS_le_of_cnt {o e : Fin 3} {a b : Fin 2 × Fin 2}
    (ha : (S.evS o e a).Nonempty) (hb : (S.evS o e b).Nonempty)
    (h : weights.cnt ((event fun ω : Ω => ω.1.1.2 ≠ 0) ∩ S.evS o e a) * weights.cnt (S.evS o e b) ≤
      weights.cnt ((event fun ω : Ω => ω.1.1.2 ≠ 0) ∩ S.evS o e b) * weights.cnt (S.evS o e a)) :
    S.modS o e a ≤ S.modS o e b := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq]
  exact condProbJunk_le_of_cnt weights ha hb h

/-- **The pill is modifying with probability `3/4` and "nothing" with probability `1/4`** at every
light input — the paper's "merely some probabilistic relationship", with the pill's probability
of taking effect a parameter of the prior (`tie`).
Source: mandate T2(b); the C&T LaTeX draft (Modification)
Kind: N+
Fidelity: variant: `m(pill) = 3/4`, `m(nothing) = 1/4` (the choice takes effect in law, not surely)
Hyps: none -/
theorem modS_light (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) :
    S.modS o e (1, r) = 3 / 4 ∧ S.modS o e (0, r) = 1 / 4 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq, show S.μ.w = weights.w from rfl,
    condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (1, r)),
    condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (0, r))]
  have h1 : weights.cnt ((event fun ω : Ω => ω.1.1.2 ≠ 0) ∩ S.evS o e (1, r)) = 96 ∧
      weights.cnt (S.evS o e (1, r)) = 128 ∧
      weights.cnt ((event fun ω : Ω => ω.1.1.2 ≠ 0) ∩ S.evS o e (0, r)) = 32 ∧
      weights.cnt (S.evS o e (0, r)) = 128 := by
    simp only [evS_eq]
    revert o e he r
    decide +kernel
  rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  norm_num

/-- **"Nothing" is minimally modifying at every light input** (`1/4 ≤ 3/4`, `1/4 ≤ 1/4`).
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem minMod_nothing (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) : S.MinMod o e (0, r) := by
  intro a' ha'
  refine modS_le_of_cnt (evS_light_nonempty o e he (0, r)) ha' ?_
  simp only [evS_eq]
  revert o e he r a'
  decide +kernel

/-- **The pill is not minimally modifying at a light input** (`3/4 > 1/4`).
Source: mandate T2(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_pill (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) : ¬ S.MinMod o e (1, r) := by
  intro h
  have := h (0, r) (evS_light_nonempty o e he (0, r))
  rw [(modS_light o e he r).1, (modS_light o e he r).2] at this
  linarith

/-! ### No communicative alternative, for the paper's reason -/

/-- Supporting lemma: the CA identity fails as a count inequality against every "nothing"
action — at the profile `(light ↦ r, asked ↦ r)`: `80 · 128 ≠ 112 · 128` when `r₂ = r`,
`80 · 128 ≠ 0 · 128` when `r₂ ≠ r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ca_key : ∀ (o e : Fin 3), e ≠ 2 → ∀ r r₂ : Fin 2,
    weights.cnt ((event fun ω : Ω => (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun _ => r) ∩
        S.evS o e (1, r)) * weights.cnt (S.evS o e (0, r₂)) ≠
      weights.cnt ((event fun ω : Ω => (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun _ => r) ∩
        S.evS o e (0, r₂)) * weights.cnt (S.evS o e (1, r)) := by
  simp only [evS_eq]
  decide +kernel

/-- **No action is a communicative alternative of the pill at a light input — for the paper's
reason.** The minimally modifying actions are the "nothing" actions, and the law of `Π̈` given
`(pill, r)` differs from the law given `(nothing, r₂)` at the profile `(light ↦ r, asked ↦ r)`:
`5/8` against `7/8` (same `r₂`) or `0` (other `r₂`). The separation is at the **report**
coordinate when `r₂ = r` (`report_law_differs`), not at a coordinate that reveals the choice —
`Π̈` hides `c'` (`polE_hides_pill`). Contrast `Mem.not_isCA_pill` (flagged: the separation there
is the representation's leak).
Source: [[examples-revisited]] Example 2 ("Corrected takeaway"); [[communication-trust-translated]] line 164; mandate T2(b)
Kind: N+
Fidelity: exact (on this representation): the CA identity fails at the coordinate the pill acts on
Hyps: none; §3 (c) -/
theorem not_isCA_pill (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) (c : Fin 2 × Fin 2) :
    ¬ S.IsCA o e (1, r) c := by
  rintro ⟨hmm, hca⟩
  obtain ⟨c₂, r₂⟩ := c
  rcases fin2_cases c₂ with rfl | rfl
  · have := hca fun _ => r
    rw [(ConcreteDS.evFollowsR_eq_univ_iff S).1 followsR, Finset.inter_univ, evPolE_eq,
      show S.μ.w = weights.w from rfl,
      condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (1, r)),
      condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (0, r₂))] at this
    have hd1 : (weights.cnt (S.evS o e (1, r)) : ℝ) ≠ 0 := by
      exact_mod_cast weights.cnt_ne_zero_of_nonempty (evS_light_nonempty o e he (1, r))
    have hd2 : (weights.cnt (S.evS o e (0, r₂)) : ℝ) ≠ 0 := by
      exact_mod_cast weights.cnt_ne_zero_of_nonempty (evS_light_nonempty o e he (0, r₂))
    rw [div_eq_div_iff hd1 hd2] at this
    exact ca_key o e he r r₂ (by exact_mod_cast this)
  · exact not_minMod_pill o e he r₂ hmm

/-- **`MemI.S` has no communicative alternatives**: the pill at a light input is attained and has
none (`not_isCA_pill`).
Source: mandate T2(b)
Kind: N+
Fidelity: exact (on this representation)
Hyps: none; §3 (c) -/
theorem not_hasCA : ¬ S.HasCA := fun h => by
  obtain ⟨c, hc⟩ := h 0 0 (1, 0) (evS_light_nonempty 0 0 (by decide) (1, 0))
  exact not_isCA_pill 0 0 (by decide) 0 c hc

/-- Supporting lemma: the report coordinate's count inequality (`80 · 128 ≠ 112 · 128`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem report_key : ∀ (o e : Fin 3), e ≠ 2 → ∀ r : Fin 2,
    weights.cnt ((event fun ω : Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = r) ∩ S.evS o e (1, r)) *
        weights.cnt (S.evS o e (0, r)) ≠
      weights.cnt ((event fun ω : Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = r) ∩ S.evS o e (0, r)) *
        weights.cnt (S.evS o e (1, r)) := by
  simp only [evS_eq]
  decide +kernel

/-- **At every light input the report's law differs given the pill and given "nothing" with the
same unforced report**: `P(Π̈(asked) = r ∣ Π*(ȯ, ö) = (pill, r)) = 5/8 ≠ 7/8 =
P(Π̈(asked) = r ∣ Π*(ȯ, ö) = (nothing, r))` — the pill decouples the report from the unforced
report policy, which is the paper's reason the Memory Problem lacks communicative alternatives.
The counterpart of `Mem.asked_law_agrees`, where the two laws coincided and the CA failure was
the representation's.
Source: [[communication-trust-translated]] line 164; audit r2 fidelity N2
Kind: N+
Fidelity: exact (computed)
Hyps: none -/
theorem report_law_differs (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) :
    condProbJunk S.μ.w (event fun ω : Ω => S.polE ω 2 = r) (S.evS o e (1, r)) 0 ≠
      condProbJunk S.μ.w (event fun ω : Ω => S.polE ω 2 = r) (S.evS o e (0, r)) 0 := by
  have h1 : (event fun ω : Ω => S.polE ω 2 = r) =
      event fun ω : Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = r :=
    event_congr fun ω => by rw [polE_eq]
  rw [h1, show S.μ.w = weights.w from rfl,
    condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (1, r)),
    condProbJunk_eq_cnt_div weights _ (evS_light_nonempty o e he (0, r))]
  have hd1 : (weights.cnt (S.evS o e (1, r)) : ℝ) ≠ 0 := by
    exact_mod_cast weights.cnt_ne_zero_of_nonempty (evS_light_nonempty o e he (1, r))
  have hd2 : (weights.cnt (S.evS o e (0, r)) : ℝ) ≠ 0 := by
    exact_mod_cast weights.cnt_ne_zero_of_nonempty (evS_light_nonempty o e he (0, r))
  intro h
  rw [div_eq_div_iff hd1 hd2] at h
  exact report_key o e he r (by exact_mod_cast h)

/-! ### The pill is preferred; the Self-Trust conclusion fails -/

/-- Supporting lemma `score_lt_of_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_lt_of_cnt {o e : Fin 3} {a b : Fin 2 × Fin 2}
    (ha : (S.evS o e a).Nonempty) (hb : (S.evS o e b).Nonempty)
    (h : csum weights u (S.evS o e a) * weights.cnt (S.evS o e b) <
      csum weights u (S.evS o e b) * weights.cnt (S.evS o e a)) :
    S.score o e a < S.score o e b :=
  condExpJunk_natDiv_lt weights u (by norm_num) ha hb h (-1)

/-- **The pill is strictly preferred at every light input**:
`E[U ∣ nothing, r] = 38/128 = 19/64 < 25/64 = 50/128 = E[U ∣ pill, r]` — a preference for the
`3/4` chance that the pill takes and then matches the light `7 : 1` (the colour is not chosen,
as on `Mem`).
Source: [[communication-trust-translated]] line 163 ("it will take the pill"); mandate T2(c)
Kind: P
Fidelity: exact (computed) on the witness; variant against the source (the gamble)
Hyps: none -/
theorem score_light (o e : Fin 3) (he : e ≠ 2) (r : Fin 2) :
    S.score o e (0, r) < S.score o e (1, r) := by
  refine score_lt_of_cnt (evS_light_nonempty o e he (0, r)) (evS_light_nonempty o e he (1, r)) ?_
  simp only [evS_eq]
  revert o e he r
  decide +kernel

/-- **The repaired Self-Trust conclusion fails at every light input of `MemI`**: the argmax
actions are the pill actions, which are not minimally modifying — as it must, since both
decision-determination (`not_decisionDetermined`) and communicative alternatives (`not_hasCA`)
fail here.
Source: mandate T2(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_argmax (o e : Fin 3) (he : e ≠ 2) :
    ¬ ∃ a, S.MinMod o e a ∧ IsArgmax (S.score o e) a := by
  rintro ⟨⟨c, r⟩, hmm, harg⟩
  rcases fin2_cases c with rfl | rfl
  · exact absurd (harg (1, r)) (not_le.2 (score_light o e he r))
  · exact not_minMod_pill o e he r hmm

end MemI

end Cleanroom.Udt.UdtCtExamples
