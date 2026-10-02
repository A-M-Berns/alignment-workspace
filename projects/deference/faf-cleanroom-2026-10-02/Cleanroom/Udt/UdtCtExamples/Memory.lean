import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt

/-!
# `Cleanroom.Udt.UdtCtExamples.Memory`: the Memory Problem (T2)

Work package `udt-ct-examples`, target T2. Source: [[communication-trust-translated]] lines
159–166 (the example; "the pill was allowed to accomplish something which the agent's own memory
was not allowed to do"), [[examples-revisited]] Example 2 (corrected 2026-08-05: "**Not in
decision-determination.** … The problem *is* decision-determined in the relevant sense").

## The structure `Mem.S`

Worlds `((d, r), (ö, ℓ))`, 24 of them:
* `d : Fin 3` — the channel state, the internal dynamic `D_I`, the internal observation `Ȯ` and
  the side channel `Ǒ` at every instance: `0` no pill, `1` the red pill (forces the report
  "red"), `2` the green pill (forces "green").
* `r : Fin 2` — the unforced report policy (the boundary dynamic `D_B`): what the agent reports
  when no pill forces it; it cannot depend on the light because the asked instance's external
  observation does not show it (memory wiped).
* `ö : Fin 2` — the focal instance, `0` the light instance, `1` the asked instance.
* `ℓ : Fin 2` — the light, an environment coordinate; the light instance's external observation
  is `Ö = ℓ` (two instances `light-red`, `light-green`, the paper's instances-by-observation), the
  asked instance's is `Ö = 2`.

External action `Ä`: at the light instance the pill choice (`0` none, `1` take the pill), **as an
external action** — the same modelling substitution as `CB` (see `CoordButtons.lean`): the
abstract structure's `I_fac` makes any internal action support-independent of `D_I`, where the
side channel lives. At the asked instance, the report: forced by the pill (`d − 1`) when
`d ≠ 0`, else `r`. `U = 1` iff the focal instance is asked and the report is the light.

**The pill content is support-independent of the light** (`IB_fac`: every `(Ö, D_{I,B})` pair is
realized, and `d ∈ D_I`): "the pill matching the light" is a correlation in law only — under the
prior, given a pill was taken, the light is the pill's colour with weight `7 : 1`. The chosen
policy `Π*` at the light input is the pill choice; at the asked input, `r`.

Weights: light worlds `1` each; asked worlds `4` each without a pill (the unforced report is
uncorrelated with the light), `7 : 1` towards the pill's colour with one. Total `60`. The weight
factors as `f(d, r) · g(ö, ℓ ∣ Π̈(d, r))`, so decision-determination clause (2) holds — **because
`Π̈(light) = [d ≠ 0]` reveals whether a pill was taken** (every `Π̈`-atom contains a single `d`:
the light coordinate separates `d = 0` from `d ≠ 0`, the asked coordinate separates `d = 1` from
`d = 2`). It is not, as the first report said, `Π̈(asked)` that carries the content: the report's
own law is a fair coin with or without a pill (`asked_law_agrees`), so it cannot screen the light
off from `d`. With the pill choice hidden from `Π̈` (`MemoryHidden.lean`, `MemH.S`: same worlds,
weights, pills and utility; `Ä(light)` the dummy `r`) clause (2) **fails** at a named atom
(`MemH.not_decisionDetermined`). The diagnosis of the Memory Problem is therefore decided by the
representation of the pill (repair round 1; findings F-15).

Two further consequences of the carrier, both disclosed in the ledger: the agent does **not**
choose the pill's *colour* — `AE = Fin 2` makes the light instance's action binary (pill / none),
and the colour is the dynamics coordinate `d`, tied to the light `7 : 1` in law (the source's
"one of two pills" offers the colour; a third report value at the asked instance would restore
the choice at 36 worlds, over the mandate's budget); and "the pill is strictly preferred"
(`score_light`) is a preference for a `7 : 1` gamble on the colour, not the source's sure pill.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace Mem

/-- Worlds `((d, r), (ö, ℓ))`.
Source: none: infrastructure (mandate T2)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 3 × Fin 2) × (Fin 2 × Fin 2)

/-- The external observation: the light at the light instance, `2` at the asked instance.
Source: [[communication-trust-translated]] line 160 (observe a light; memory wiped before the question)
Kind: D
Fidelity: exact
Hyps: n/a -/
def obs (ω : Ω) : Fin 3 := if ω.2.1 = 0 then Fin.castSucc ω.2.2 else 2

/-- The external action of dynamics `(d, r)` at instance `e`: the pill choice at a light instance
(`1` iff `d ≠ 0`), the report at the asked instance (`d − 1` if forced, else `r`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (d : Fin 3) (r : Fin 2) (e : Fin 3) : Fin 2 :=
  if e = 2 then (if d = 0 then r else if d = 1 then 0 else 1) else (if d = 0 then 0 else 1)

/-- The utility numerator: `1` iff the focal instance is asked and the report equals the light.
Source: [[communication-trust-translated]] line 160 ("rewarded for a correct answer")
Kind: D
Fidelity: exact
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 1 ∧ actOf ω.1.1 ω.1.2 (obs ω) = ω.2.2 then 1 else 0

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 1 := by revert ω; decide

/-- The chosen policy of dynamics `(d, r)`: the pill choice at a light input, `r` at the asked
input.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (d : Fin 3) (r : Fin 2) (oe : Fin 3 × Fin 3) : Fin 1 × Fin 2 :=
  (0, if oe.2 = 2 then r else if d = 0 then 0 else 1)

/-- The side-channel impact: at the asked instance a pill forces its report; nothing at the
light instances.
Source: [[communication-trust-translated]] line 160 (the two pills)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pfun (e : Fin 3) (c : Fin 3) : Option (Fin 2) :=
  if e = 2 then (if c = 0 then none else if c = 1 then some 0 else some 1) else none

/-- The weights: see the module docstring.
Source: mandate T2 (the prior)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.2.1 = 0 then 1 else if ω.1.1 = 0 then 4 else
    (if (if ω.1.1 = 1 then (0 : Fin 2) else 1) = ω.2.2 then 7 else 1)
  pos ω := by revert ω; decide
  N := 60
  sum_eq := by decide +kernel

/-- **The Memory Problem as an abstract decision structure.**
Source: [[communication-trust-translated]] lines 159–166; mandate T2
Kind: N+
Fidelity: variant: the pill choice is `Ä(light)` (module docstring); the pill's colour is not chosen (it is the dynamics coordinate `d`, correlated with the light `7 : 1` in law only); §3 (c)
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 3) (Fin 3) (Fin 1) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 3) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1.1
  oE := obs
  aI _ := 0
  aE ω := actOf ω.1.1 ω.1.2 (obs ω)
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH _ := 0
  oC ω := ω.1.1
  polS ω := polOf' ω.1.1 ω.1.2
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
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => ((if ω₂.2.1 = 0 then (if actOf ω₁.1.1 ω₁.1.2 (obs ω₁) = 0 then 0 else 1) else 0,
      actOf ω₁.1.1 ω₁.1.2 (obs ω₁)), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **The Memory Problem as a concrete decision structure**: no messages (memory is wiped; there
is no self-communication channel), the pills force the report.
Source: [[communication-trust-translated]] lines 159–166; mandate T2
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 3) (Fin 3) (Fin 1) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 3) where
  toAbstractDS := absDS
  s _ _ := none
  p := pfun

/-! ### Reading the derived objects off the coordinates -/

/-- Supporting lemma: the decidable hypotheses of `polE_eq_of`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_key :
    (∀ ω : Ω, actOf ω.1.1 ω.1.2 (obs ω) = actOf ω.1.1 ω.1.2 (obs ω)) ∧
    (∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) →
      (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf ω'.1.1 ω'.1.2 e) ∧
    (∀ (ω : Ω) (e : Fin 3), ∃ ω' : Ω, (ω'.1.1, ω'.1.2) = (ω.1.1, ω.1.2) ∧ obs ω' = e) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`Π̈` on `Mem`**: the external policy of dynamics `(d, r)` is `actOf d r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun e => actOf ω.1.1 ω.1.2 e :=
  S.polE_eq_of (fun ω e => actOf ω.1.1 ω.1.2 e) polE_key.1 polE_key.2.1 polE_key.2.2 ω

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 3 → Fin 2) :
    S.evPolE π = event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 3 × Fin 2) : S.polOf d = fun e => actOf d.1 d.2 e := by
  obtain ⟨d1, d2⟩ := d
  exact polE_eq ((d1, d2), (0, 0))

/-- Supporting lemma `evS_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (o : Fin 3) (e : Fin 3) (a : Fin 1 × Fin 2) :
    S.evS o e a = event fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, e) = a := rfl

/-- **`Π* ⊑ D_{I,B}` on `Mem`.**
Source: mandate T2(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable S.DIB S.polS := by
  show ∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) → polOf' ω.1.1 ω.1.2 = polOf' ω'.1.1 ω'.1.2
  decide +kernel

/-- **`R ⊑ D_{I,B}` on `Mem`** (silent everywhere, so this is `rfl` — a degenerate check).
Source: mandate T2
Kind: N−
Fidelity: n/a (vacuous: `R` is constant)
Hyps: none -/
theorem R_sub_DIB : IsSubvariable S.DIB S.R := fun _ _ _ => rfl

/-- **`P(Π̈ = R) = 1` on `Mem`**, vacuously (no message channel exists).
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

/-- Supporting lemma `evMod_eq`: the modified worlds are those with a pill.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : S.evMod = event fun ω : Ω => ω.1.1 ≠ 0 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 3, (pfun e ω.1.1).isSome) ↔ ω.1.1 ≠ 0
  revert ω
  decide +kernel

/-- Supporting lemma: attainment at every input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_nonempty (o e : Fin 3) (x : Fin 2) : (S.evS o e (0, x)).Nonempty := by
  rw [evS_eq]; revert o e x; decide +kernel

/-- **The prose meaning of `Π*` holds on `Mem`** (`hlink`).
Source: mandate T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω) := by
  intro ω h
  have h' : pfun (obs ω) ω.1.1 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf ω.1.1 ω.1.2 (obs ω)) = polOf' ω.1.1 ω.1.2 (ω.1.1, obs ω)
  revert ω
  decide +kernel

/-! ### Decision-determination: holds on this representation, because `Π̈(light)` carries the choice -/

/-- Supporting lemma: `U` is a function of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω,
    (actOf ω.1.1 ω.1.2 (obs ω), ω.2) = (actOf ω'.1.1 ω'.1.2 (obs ω'), ω'.2) → u ω = u ω' := by
  decide +kernel

/-- Supporting lemma: clause (2) as a count identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dd_key : ∀ (e : Fin 2 × (Fin 2 × Fin 2)) (d : Fin 3 × Fin 2),
    weights.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 (obs ω), ω.2) = e ∧ (ω.1.1, ω.1.2) = d) *
        weights.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) =
      weights.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 (obs ω), ω.2) = e ∧
          (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) *
        weights.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = d) := by
  decide +kernel

/-- **The Memory Problem is decision-determined on the representation where the pill choice is
the light instance's external action** (`Ä(light) = [d ≠ 0]`): `U ⊑ E` by `u_of_E`, and
`E ⊥ D_{I,B} ∣ Π̈` by the count identity `dd_key`. Clause (2) holds *because* `Π̈(light)` reveals
whether a pill was taken (module docstring): with the choice hidden from `Π̈` the same worlds and
weights fail clause (2) at a named atom (`MemH.not_decisionDetermined`, `MemoryHidden.lean`). So
this is a witness check on one of two representations, not a refutation of the diagnosis
[[examples-revisited]] retracted on 2026-08-05: the correction's argument — "The environment's
reward depends only on the external report … and the actual light color" — addresses clause (1),
which both representations satisfy (`MemH.U_sub_E`), and never clause (2), where the retracted
diagnosis is right on the paper's own internal-action picture of the pill (findings F-15).
Source: [[examples-revisited]] Example 2 (corrected 2026-08-05); [[communication-trust-translated]] lines 159–166, 381–390; mandate T2(a)
Kind: N+
Fidelity: variant: DD holds with the pill choice visible in `Π̈` (`Ä(light)`); clause (2) fails when it is hidden — atom `e = (red, (asked, red))`, `d = (red pill, red)` (`MemH`)
Hyps: none; §3 (c) -/
theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · show natDiv u 1 ω = natDiv u 1 ω'
    unfold natDiv
    rw [u_of_E ω ω' h]
  · have hev : (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
        event fun ω : Ω => (actOf ω.1.1 ω.1.2 (obs ω), ω.2) = e ∧
          (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)

/-! ### Modification and the missing communicative alternative -/

/-- **The pill is modifying with probability `1`, "nothing" with probability `0`** at a light
input.
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modS_light (o : Fin 3) (e : Fin 3) (he : e ≠ 2) :
    S.modS o e (0, 1) = 1 ∧ S.modS o e (0, 0) = 0 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq]
  constructor
  · refine condProbJunk_eq_one_of_subset S.pos (evS_nonempty o e 1) ?_ 0
    rw [evS_eq]
    intro ω hω
    rw [mem_event] at hω ⊢
    revert ω o e
    decide +kernel
  · refine condProbJunk_eq_zero_of_disjoint S.pos (evS_nonempty o e 0) ?_ 0
    rw [evS_eq]
    revert o e
    decide +kernel

/-- **The pill is not minimally modifying at a light input.**
Source: mandate T2(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_pill (o : Fin 3) (e : Fin 3) (he : e ≠ 2) : ¬ S.MinMod o e (0, 1) := by
  intro h
  have := h (0, 0) (evS_nonempty o e 0)
  rw [(modS_light o e he).1, (modS_light o e he).2] at this
  linarith

/-- Supporting lemma `score_lt_of_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_lt_of_cnt {o e : Fin 3} {a b : Fin 1 × Fin 2}
    (ha : (S.evS o e a).Nonempty) (hb : (S.evS o e b).Nonempty)
    (h : csum weights u (S.evS o e a) * weights.cnt (S.evS o e b) <
      csum weights u (S.evS o e b) * weights.cnt (S.evS o e a)) :
    S.score o e a < S.score o e b :=
  condExpJunk_natDiv_lt weights u (by norm_num) ha hb h (-1)

/-- **The pill is strictly preferred at a light input**: `E[U ∣ nothing] = 2/5 < 7/10 = E[U ∣ pill]`
— UDT "will take the pill to modify its behavior" (udt-rep-025(b)).
Source: [[communication-trust-translated]] line 163 ("Clearly, UDT lacks self-trust in this example; it will take the pill")
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem score_light (o : Fin 3) (e : Fin 3) (he : e ≠ 2) :
    S.score o e (0, 0) < S.score o e (0, 1) := by
  refine score_lt_of_cnt (evS_nonempty o e 0) (evS_nonempty o e 1) ?_
  rw [evS_eq, evS_eq]
  revert o e
  decide +kernel

/-- Supporting lemma: the pill profile `(light ↦ pill, asked ↦ red)` is attained together with the
pill at every light input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pill_profile_pos : ∀ o e : Fin 3, e ≠ 2 →
    0 < weights.cnt ((event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) ∩
      event fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, e) = (0, 1)) := by
  decide +kernel

/-- Supporting lemma: the pill profile never occurs with "nothing" at a light input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pill_profile_disj : ∀ o e : Fin 3, e ≠ 2 →
    (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) ∩
      event (fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, e) = (0, 0)) = ∅ := by
  decide +kernel

/-- **No action is a communicative alternative of the pill at a light input — through the
representation.** The only minimally modifying action is "nothing", and the pill profile
`(light ↦ pill, asked ↦ red)` has positive mass given the pill and mass `0` given "nothing"
(with `{Π̈ = R} = Ω`). The separation is at the **light** coordinate of `Π̈`, which is the pill
choice itself on this carrier (`Ä(light) = [d ≠ 0]`, findings F-1): the **asked** coordinate —
the report, the only coordinate the paper's Memory Problem is about — has the *same* conditional
law given the pill and given "nothing" at every light input (`asked_law_agrees`, both `1/2`).
So this is the same representation artifact the package flags on `TB.not_isCA_pill_msg`, not the
paper's reason, and it does not show where the Memory Problem substantively leaves the Self-Trust
theorem's scope: on the hidden-pill representation (`MemH`) decision-determination fails instead
(findings F-15).
Source: [[examples-revisited]] Example 2 ("Corrected takeaway"); [[communication-trust-translated]] line 164; mandate T2(b)
Kind: N−
Fidelity: weaker: holds through the representation (`Π̈(light)` reveals the choice); the report's law is identical under both actions — degenerate on the paper's coordinate (Kind regraded from `L`, audit r2 adversarial N5)
Hyps: (c) 2 (the choice as `Ä(light)`) -/
theorem not_isCA_pill (o : Fin 3) (e : Fin 3) (he : e ≠ 2) (c : Fin 1 × Fin 2) :
    ¬ S.IsCA o e (0, 1) c := by
  rintro ⟨hmm, hca⟩
  obtain ⟨ai, x⟩ := c
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · have := hca fun e' => actOf 1 0 e'
    rw [(ConcreteDS.evFollowsR_eq_univ_iff S).1 followsR, Finset.inter_univ, evPolE_eq,
      condProbJunk_eq_zero_of_disjoint S.pos (evS_nonempty o e 0) (pill_profile_disj o e he),
      show S.μ.w = weights.w from rfl, condProbJunk_eq_cnt_div weights _ (evS_nonempty o e 1)] at this
    have hc : (weights.cnt ((event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) =
        fun e => actOf 1 0 e) ∩ S.evS o e (0, 1)) : ℝ) ≠ 0 := by
      exact_mod_cast (pill_profile_pos o e he).ne'
    have hd : (weights.cnt (S.evS o e (0, 1)) : ℝ) ≠ 0 := by
      exact_mod_cast weights.cnt_ne_zero_of_nonempty (evS_nonempty o e 1)
    exact hc ((div_eq_zero_iff.1 this).resolve_right hd)
  · exact not_minMod_pill o e he hmm

/-- **`Mem.S` has no communicative alternatives**: the pill at a light input is attained and has
none — through the representation, as `not_isCA_pill`.
Source: mandate T2(b)
Kind: N−
Fidelity: weaker: holds through the representation (as `not_isCA_pill`)
Hyps: (c) 2 -/
theorem not_hasCA : ¬ S.HasCA := fun h => by
  obtain ⟨c, hc⟩ := h 0 0 (0, 1) (evS_nonempty 0 0 1)
  exact not_isCA_pill 0 0 (by decide) c hc

/-- **At every light input the report's law is the same given the pill and given "nothing"**:
`P(Π̈(asked) = x ∣ Π*(ȯ, ö) = pill) = P(Π̈(asked) = x ∣ Π*(ȯ, ö) = nothing)` for both `x` (both
`1/2`). Restricted to the coordinate the pill acts on, the two laws of `Π̈` agree exactly; the CA
identity in `not_isCA_pill` fails only where `Π̈` reveals the choice. Lifted from the audit-r1
probes `MemMarginal.asked_marginal_agrees` / `MemAskedLaw.mem_asked_law_agrees` (repair round 1).
Source: audit r1 (fidelity B1, adversarial B2); [[communication-trust-translated]] line 164
Kind: L
Fidelity: exact (computed)
Hyps: none -/
theorem asked_law_agrees (o e : Fin 3) (he : e ≠ 2) (x : Fin 2) :
    condProbJunk S.μ.w (event fun ω : Ω => S.polE ω 2 = x) (S.evS o e (0, 1)) 0 =
      condProbJunk S.μ.w (event fun ω : Ω => S.polE ω 2 = x) (S.evS o e (0, 0)) 0 := by
  have h1 : (event fun ω : Ω => S.polE ω 2 = x) =
      event fun ω : Ω => actOf ω.1.1 ω.1.2 2 = x :=
    event_congr fun ω => by rw [polE_eq]
  rw [h1, show S.μ.w = weights.w from rfl]
  clear h1
  refine weights.condProbJunk_eq_of_cnt (evS_nonempty o e 1) (evS_nonempty o e 0) ?_
  rw [evS_eq, evS_eq]
  revert o e he x
  decide +kernel

/-- **The repaired Self-Trust conclusion fails at a light input**: the pill is the unique argmax
and is not minimally modifying.
Source: mandate T2(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_argmax (o : Fin 3) (e : Fin 3) (he : e ≠ 2) :
    ¬ ∃ a, S.MinMod o e a ∧ IsArgmax (S.score o e) a := by
  rintro ⟨⟨ai, x⟩, hmm, harg⟩
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · exact absurd (harg (0, 1)) (not_le.2 (score_light o e he))
  · exact not_minMod_pill o e he hmm

/-! ### T2(d): the unforced report is uncorrelated with the light -/

/-- **Under no pill, the two reports score the same** at the asked input restricted to the
unmodified worlds: `E[U ∣ Π*(ȯ, asked) = red, no pill] = E[U ∣ Π*(ȯ, asked) = green, no pill]`
(both `2/5`: the report is uncorrelated with the light, and the asked instance carries mass
`4/5`). At the asked input without the restriction the two reports also tie, at `3/5`, because
the pill worlds contribute equally to both.
Source: mandate T2(d)
Kind: L
Fidelity: n/a (the tie; the "`1/2`" of the mandate is the value conditional on being asked)
Hyps: none -/
theorem report_tie (o : Fin 3) :
    condExpJunk S.μ.w S.U (S.evS o 2 (0, 0) ∩ event fun ω : Ω => ω.1.1 = 0) (-1) =
      condExpJunk S.μ.w S.U (S.evS o 2 (0, 1) ∩ event fun ω : Ω => ω.1.1 = 0) (-1) := by
  refine condExpJunk_natDiv_eq weights u (by norm_num) ?_ ?_ ?_ (-1)
  · rw [evS_eq]; revert o; decide +kernel
  · rw [evS_eq]; revert o; decide +kernel
  · rw [evS_eq, evS_eq]; revert o; decide +kernel

end Mem

end Cleanroom.Udt.UdtCtExamples
