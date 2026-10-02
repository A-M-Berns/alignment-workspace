import Cleanroom.Decision.DpFirstpersonSc.License
import Cleanroom.Decision.DpFirstpersonSc.Lift
import Cleanroom.Decision.DpFirstpersonSc.Grades
import Cleanroom.Decision.DpCalibration.Chain
import Cleanroom.Udt.UdtSupercondition.Coherence
import Cleanroom.Udt.UdtSupercondition.Canonical

/-!
# The dogmatic epistemology, Proposition 1 against SC, and calibrated refinement — T6/T7 of
[[dp-firstperson-sc-mandate]]

* `Reachable C B d := 0 < μ(occ(d))`; **`DogmaticEpistemology s₀ s obs C B`** (Definition 19,
  decision 4): every *reachable* queried state agrees with the Jeffrey conditioning of `s₀` at
  its observation, with the existential guard `0 < P_{s₀}(O_d)` — a reachable point whose
  observation is `s₀`-null is *not* dogmatic.
* **T6(a), AN-14(i)** (`dogmatic_downstream`, `dogmatic_epistemicallyCoherent`): under the
  dogmatic epistemology each reachable `(s₀, s_d)` is `Downstream` in SC's sense, hence
  `EpistemicallyCoherent` (SC Def 12.1) by `udt-supercondition`'s collapse
  `epistemicallyCoherent_iff_condOn` — one line, which is why it is `L`.
* **T6(b), the converse of Proposition 1** (`strictOC_imp_dogmatic`, `dogmatic_imp_strictOC`,
  `strictOC_iff_dogmatic`): over a Definition-11 prior-calibrated `s₀`, strict OC at every
  queried point ⟹ dogmatic **when `ν(O_d) > 0` at every reachable queried point** (AN-14(ii)'s
  hypothesis), and dogmatic ⟹ strict OC **when every queried point with `ν(O_d) > 0` is
  reachable** — the second hypothesis is missing from AN-14(ii) and is needed (finding F3,
  witness `WitnessesDogmatic.lean`). Proposition 1 itself is `dp-calibration`'s
  `priorCalibrated_jeffrey_strictOC` (cited; `strictOC_of_jeffrey_agree` is its agreement form).
* **T6(d)** (`dogmatic_value_clause`): the value clause `V_{s_d}(X) = 𝔼_μ[r | X ∧ O_d]` is a
  theorem given Definition 11 — the *analogue* of SC Claim 12.3 (DNI-5: not a result), approximate
  grade (dossier T7's `V` column).
* **T6(e)** (`dogmatic_calibratedRefinement`, `lift_calibratedRefinement`): Proposition 1 is Def
  6.2's no-refinement case and Proposition 2 its refinement case — both `L` by
  `refinement_posteriors_eq_condOn` (which makes Def 6.2 the event-conditioning reading).
* **T7(a)** (`strictState_calibratedRefinement`, `strictState_calibratedRefinement_pushdown`;
  repair round 2): the strict-OC posterior `μ(· | λ⁻¹O_d)` is a Def-6.2 refinement posterior for
  every structure and pushes down to the strict-OC state — admitting the observation event reaches
  every strict-OC state. `calibratedRefinement_as_idle`: the structure's admitted atoms are idle
  in that clause, so "occurrence atoms only" is imposed by `OccOnlyPosterior`'s predicate.
* **T7(b), AN-9/AN-10** (`occOnly_posteriors`, `an10_compatible_iff_ac`): on the lifted prior
  with the occurrence anticipation, a refinement whose finer atoms are the occurrence atoms of
  `d` alone reaches only `μ(· | occ)`, `μ(· | occᶜ)` or `μ`; with `Ĉ = 𝓔` via `(λ, id)` the range
  condition of `commonInfo_condModel_iff` is automatic and compatibility reads `P_s ≪ ν`.

Vocabulary: `Downstream`, `EpistemicallyCoherent`, `CalibratedRefinement` are SC's; "coherent"
below is never v2's Definition 22.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Definition 19 -/

section defs

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Reachable**: the point `d` is consulted with positive probability, `μ(occ(d)) > 0`.
Source: [[decision-problems-v2]] Definition 19 ("the queried decision-points that the pair can
reach"); mandate decision 4
Kind: D -/
def Reachable (d : ι) : Prop := 0 < Tree.mass C B (occ d B)

/-- **The dogmatic epistemology relative to `s₀`** (Definition 19): every reachable queried
state is the Jeffrey conditioning of `s₀` at its observation — with the existential guard
`0 < P_{s₀}(O_d)`: a reachable point whose observation `s₀` rules out is *not* dogmatic.
Agreement modulo `V`'s junk values (`State.Agree`), since `V` is read only on positive events.
Source: [[decision-problems-v2]] Definition 19 ("every reachable queried state is the Jeffrey
conditioning of `s₀` at its observation, as in Proposition 1"); `anticipation.md` AN-14(ii)
Kind: D
Fidelity: variant: agreement modulo `V`'s junk values; "reachable" rendered as `μ(occ(d)) > 0` -/
def DogmaticEpistemology (s₀ : State Ω K) (s : ι → State Ω K) : Prop :=
  ∀ d ∈ queried B, Reachable C B d →
    ∃ h : 0 < s₀.pr (obs d), State.Agree (s d) (jeffreyCond s₀ (obs d) h)

/-- The strict clauses transfer along agreement. Source: none: infrastructure. Kind: L -/
theorem strictClausesAt_congr_agree (s : ι → State Ω K) (t : State Ω K) (d : ι)
    (hag : State.Agree (s d) t) (ht : StrictClausesAt (fun _ => t) obs C B d) :
    StrictClausesAt s obs C B d := by
  refine ⟨fun X => ?_, fun X hX hXO => ?_⟩
  · have := ht.1 X
    simp only [State.pr, hag.1] at this ⊢
    exact this
  · rw [hag.2 X hX]
    exact ht.2 X (by simpa [State.pr, ← hag.1] using hX) hXO

/-- At `O` itself, the calibrated state is the prior state Jeffrey-conditioned on `O`.
Source: [[decision-problems-v2]] Proposition 1 proof
Kind: L -/
theorem agree_calibratedState_jeffreyCond_self (O : Finset Ω) (hO : 0 < nu C B O)
    (hE : 0 < (priorState C B).pr O) :
    State.Agree (calibratedState C B O hO) (jeffreyCond (priorState C B) O hE) := by
  rw [agree_calibratedState_jeffreyCond_iff]
  simp

/-- Over a prior-calibrated `s₀`, the calibrated state at `O` agrees with `jeffreyCond s₀ O`.
Source: [[decision-problems-v2]] Proposition 1
Kind: L -/
theorem agree_calibratedState_jeffreyCond_of_priorCalibrated {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀) (O : Finset Ω) (hO : 0 < nu C B O) (h : 0 < s₀.pr O) :
    State.Agree (calibratedState C B O hO) (jeffreyCond s₀ O h) := by
  have hag := agree_priorState_of_priorCalibrated C B hcal
  have hE : 0 < (priorState C B).pr O := by
    show 0 < probOf (priorState C B).P O
    rw [← hag.1]; exact h
  exact (agree_calibratedState_jeffreyCond_self C B O hO hE).trans
    (jeffreyCond_agree hag.symm O hE h)

end defs

/-! ## T6(b): Proposition 1 and its converse -/

section converse

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Proposition 1, agreement form**: a prior-calibrated `s₀` with every queried state agreeing
with its Jeffrey conditioning wherever defined gives strict OC. The equality form is
`dp-calibration`'s `priorCalibrated_jeffrey_strictOC` (Chain.lean), cited; this is the same
argument modulo `V`'s junk values.
Source: [[decision-problems-v2]] §3.1 Proposition 1
Kind: C
Fidelity: exact (agreement in place of equality)
Hyps: (a) `PriorCalibrated C B s₀`, (a) the Jeffrey hypothesis wherever `P_{s₀}(O_d) > 0` -/
theorem strictOC_of_jeffrey_agree (s : ι → State Ω K) {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀)
    (hs : ∀ d ∈ queried B, ∀ h : 0 < s₀.pr (obs d), State.Agree (s d) (jeffreyCond s₀ (obs d) h)) :
    StrictOC s obs C B := by
  intro d hd hO
  have h : 0 < s₀.pr (obs d) := by rw [hcal.1]; exact hO
  refine strictClausesAt_congr_agree obs C B s (calibratedState C B (obs d) hO) d ?_
    (strictClausesAt_calibratedState obs C B _ d hO rfl)
  exact (hs d hd h).trans
    (agree_calibratedState_jeffreyCond_of_priorCalibrated C B hcal (obs d) hO h).symm

/-- **The converse of Proposition 1, `⟹`** (AN-14(ii)): over a prior-calibrated `s₀`, if
`ν(O_d) > 0` at every reachable queried point then strict OC implies the dogmatic epistemology.
Source: `anticipation.md` AN-14(ii) ("Converse, with hypothesis `ν(O_d) > 0` at every reachable
queried point: strict OC at every queried point ⟺ the dogmatic epistemology")
Kind: C (chains `strictClausesAt_unique`, `strictClausesAt_calibratedState` and
`agree_calibratedState_jeffreyCond_of_priorCalibrated`; the content is the hypothesis analysis, F3)
Fidelity: exact (this direction needs exactly the stated hypothesis)
Hyps: (a) `PriorCalibrated C B s₀`, (a) `Reachable d → 0 < ν(O_d)` on queried points -/
theorem strictOC_imp_dogmatic (s : ι → State Ω K) {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀)
    (hreach : ∀ d ∈ queried B, Reachable C B d → 0 < nu C B (obs d))
    (hoc : StrictOC s obs C B) : DogmaticEpistemology obs C B s₀ s := by
  intro d hd hr
  have hO : 0 < nu C B (obs d) := hreach d hd hr
  have h : 0 < s₀.pr (obs d) := by rw [hcal.1]; exact hO
  refine ⟨h, ?_⟩
  have hu := strictClausesAt_unique obs C B s (fun _ => calibratedState C B (obs d) hO) d hO
    (hoc d hd hO) (strictClausesAt_calibratedState obs C B _ d hO rfl)
  exact hu.trans (agree_calibratedState_jeffreyCond_of_priorCalibrated C B hcal (obs d) hO h)

/-- **The converse of Proposition 1, `⟸`**: the dogmatic epistemology implies strict OC
**provided every queried point with `ν(O_d) > 0` is reachable** — a hypothesis AN-14(ii) does not
state and which is needed (`WitnessesDogmatic.lean`, `tys_dogmatic_not_strictOC`).
Source: `anticipation.md` AN-14(ii); [[decision-problems-v2]] Proposition 1, Definition 19
Kind: C (the mirror chain of `strictOC_imp_dogmatic`)
Fidelity: exact (with the missing hypothesis supplied)
Hyps: (a) `PriorCalibrated C B s₀`, (a) `0 < ν(O_d) → Reachable d` on queried points -/
theorem dogmatic_imp_strictOC (s : ι → State Ω K) {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀)
    (hreach : ∀ d ∈ queried B, 0 < nu C B (obs d) → Reachable C B d)
    (hdog : DogmaticEpistemology obs C B s₀ s) : StrictOC s obs C B := by
  intro d hd hO
  obtain ⟨h, hag⟩ := hdog d hd (hreach d hd hO)
  refine strictClausesAt_congr_agree obs C B s (calibratedState C B (obs d) hO) d ?_
    (strictClausesAt_calibratedState obs C B _ d hO rfl)
  exact hag.trans (agree_calibratedState_jeffreyCond_of_priorCalibrated C B hcal (obs d) hO h).symm

/-- **T6(b), the converse of Proposition 1 as an iff**: over a prior-calibrated `s₀`, when
reachability and `ν(O_d) > 0` coincide at every queried point, strict OC ⟺ the dogmatic
epistemology relative to `s₀`. Without the first half the `⟹` fails (TN-V2, `p = 1`, `(1,1)`,
`WitnessesDogmatic.lean`); without the second the `⟸` fails (Told-You-So under take-5 with
`O = ⊤`).
Source: `anticipation.md` AN-14(ii); [[decision-problems-v2]] Definition 19; dossier T7, XC-12
Kind: C (the two directions conjoined)
Fidelity: variant: both coincidence hypotheses (the source states one)
Hyps: (a) `PriorCalibrated C B s₀`, (a) `Reachable d ↔ 0 < ν(O_d)` on queried points -/
theorem strictOC_iff_dogmatic (s : ι → State Ω K) {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀)
    (hreach : ∀ d ∈ queried B, (Reachable C B d ↔ 0 < nu C B (obs d))) :
    StrictOC s obs C B ↔ DogmaticEpistemology obs C B s₀ s :=
  ⟨strictOC_imp_dogmatic obs C B s hcal (fun d hd => (hreach d hd).mp),
    dogmatic_imp_strictOC obs C B s hcal (fun d hd => (hreach d hd).mpr)⟩

/-- **T6(d), the value clause**: under the dogmatic epistemology over a prior-calibrated `s₀`,
at a reachable queried point with `ν(O_d) > 0`, `V_{s_d}(X) · ν(X ∧ O_d) = 𝔼_μ[r · 1_{X ∧ O_d}]`
on positive events — Proposition 1's second equality, a theorem given Definition 11's value
clause. It is only the *analogue* of SC Claim 12.3 (`𝔼_{X_i}[u | ā₀] = 𝔼_{X_j}[u]`, DNI-5: an
unproven claim, not to be cited as a result): v2's desirability has its own clause, SC a fixed
utility.
Source: `anticipation.md` AN-14(iii); `bridge-dossier.md` T7 (`V`-column, approximate), XC-12
Kind: L
Fidelity: exact for v2; approximate as a dictionary row
Hyps: (a) `PriorCalibrated C B s₀`, (a) dogmatic at `d`, (a) `0 < ν(O_d)` -/
theorem dogmatic_value_clause (s : ι → State Ω K) {s₀ : State Ω K}
    (hcal : PriorCalibrated C B s₀) (hdog : DogmaticEpistemology obs C B s₀ s) {d : ι}
    (hd : d ∈ queried B) (hr : Reachable C B d) (hO : 0 < nu C B (obs d)) :
    StrictClause2At s obs C B d := by
  obtain ⟨h, hag⟩ := hdog d hd hr
  exact (strictClausesAt_congr_agree obs C B s (calibratedState C B (obs d) hO) d
    (hag.trans (agree_calibratedState_jeffreyCond_of_priorCalibrated C B hcal (obs d) hO h).symm)
    (strictClausesAt_calibratedState obs C B _ d hO rfl)).2

end converse

/-! ## T6(a)(e): against SC's Def 12.1 and Def 6.2 -/

section sc

variable (obs : ι → Finset Ω) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)

/-- **T6(a), AN-14(i)**: under the dogmatic epistemology, each reachable queried state is
`Downstream` of `s₀` in SC's sense (a Bayesian conditioning on a positive event).
Source: `anticipation.md` AN-14(i) ("Def 12.1 reduces to '`X_j` is `X_i` conditioned on some
positive-probability event'"); dossier T7
Kind: L
Fidelity: exact on the `P`-component (disjoint observations; with overlapping observations the
§4.6 Jeffrey form — not built)
Hyps: (a) dogmatic -/
theorem dogmatic_downstream {s₀ : State Ω ℚ} {s : ι → State Ω ℚ}
    (hdog : DogmaticEpistemology obs C B s₀ s) {d : ι} (hd : d ∈ queried B)
    (hr : Reachable C B d) : Downstream (toPMF s₀.P) (toPMF (s d).P) := by
  obtain ⟨h, hag⟩ := hdog d hd hr
  refine ⟨(↑(obs d) : Set Ω), (mass_toPMF_pos_iff s₀.P (obs d)).mpr h, ?_⟩
  rw [hag.1, ← condOn_toPMF_jeffrey]

/-- **Proposition 1's hypothesis makes `(s₀, s_d)` epistemically coherent** (SC Def 12.1) — by
the collapse `epistemicallyCoherent_iff_condOn` (`udt-supercondition`'s finding that Def 12.1 is
`Downstream`), which is why this is one line.
Source: `anticipation.md` AN-14(i); `bridge-dossier.md` T7 ("exact on the `P`-component")
Kind: L
Fidelity: exact on `P` (disjoint observations)
Hyps: (a) dogmatic -/
theorem dogmatic_epistemicallyCoherent {s₀ : State Ω ℚ} {s : ι → State Ω ℚ}
    (hdog : DogmaticEpistemology obs C B s₀ s) {d : ι} (hd : d ∈ queried B)
    (hr : Reachable C B d) : EpistemicallyCoherent (toPMF s₀.P) (toPMF (s d).P) :=
  (epistemicallyCoherent_iff_condOn _ _).mpr (dogmatic_downstream obs C B hdog hd hr)

/-- **T6(e), Proposition 1 as Def 6.2's no-refinement case**: a dogmatic state is a calibrated
refinement posterior of `s₀` for *every* anticipation structure — because Def 6.2's posteriors
are exactly the event conditionings (`refinement_posteriors_eq_condOn`).
Source: `anticipation.md` AN-14(iv) ("Prop 1 is Def 6.2's no-refinement case")
Kind: L -/
theorem dogmatic_calibratedRefinement {s₀ : State Ω ℚ} {s : ι → State Ω ℚ}
    (hdog : DogmaticEpistemology obs C B s₀ s) {d : ι} (hd : d ∈ queried B)
    (hr : Reachable C B d) (as : AnticipationStructure (toPMF s₀.P) Ω) :
    Nonempty (CalibratedRefinement (toPMF s₀.P) (toPMF (s d).P) as) :=
  (refinement_posteriors_eq_condOn as _).mpr (dogmatic_downstream obs C B hdog hd hr)

/-- **Proposition 2 as Def 6.2's refinement case**: the lifted state `μ(· | occ(d))` is a
calibrated refinement posterior of the run law for every anticipation structure on the leaves.
Source: `anticipation.md` AN-14(iv) ("Prop 2 the refinement case"), AN-15(a)
Kind: L -/
theorem lift_calibratedRefinement (d : ι) (h : 0 < Tree.mass C B (occ d B))
    (as : AnticipationStructure (runPMF C B) B.Leaves) :
    Nonempty (CalibratedRefinement (runPMF C B)
      (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)) as) :=
  (refinement_posteriors_eq_condOn as _).mpr ⟨_, _, rfl⟩

/-- **T7(a), the strict-OC state as a Def-6.2 refinement posterior**: the strict-OC posterior
`μ(· | λ⁻¹O_d)` is a calibrated-refinement posterior of the run law for every anticipation
structure `as` — "admitting the observation event `λ⁻¹O_d` reaches every strict-OC state"
(its pushdown is the strict-OC state's `P`, `strictState_calibratedRefinement_pushdown`). What
the structure cannot say: SC's `CalibratedRefinement` is nonempty iff the posterior is *some*
event conditioning (`refinement_posteriors_eq_condOn`), for every `as`
(`calibratedRefinement_as_idle`), so "among the finer atoms" is not a constraint SC's object
expresses — `OccOnlyPosterior` imposes it by hand. Before repair round 2 this statement was cited
to `lift_calibratedRefinement`, which conditions on `occ(d)` (audit r2 adversarial B1).
Source: `anticipation.md` AN-9 ("in general every strict-OC state is reached via `λ⁻¹(O_d)`");
mandate T7(a); audit r2 adversarial B1
Kind: L
Fidelity: exact (Def 6.2's posterior clause; the admitted atoms are not fixed by the structure)
Hyps: (a) `0 < ν(O_d)` -/
theorem strictState_calibratedRefinement (d : ι) (hO : 0 < nu C B (obs d))
    (as : AnticipationStructure (runPMF C B) B.Leaves) :
    Nonempty (CalibratedRefinement (runPMF C B)
      (condOn (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves)
        ((mass_runPMF_pos_iff C B _).mpr hO)) as) :=
  (refinement_posteriors_eq_condOn as _).mpr ⟨_, _, rfl⟩

/-- **The pushdown of the `λ⁻¹O_d`-refinement posterior is the strict-OC state's `P`** — so the
posterior of `strictState_calibratedRefinement` "reaches the strict-OC state" in the mandate's
sense (the state on `Ω`, not only the event conditioning on the leaves).
Source: `anticipation.md` AN-9; mandate T7(a); audit r2 adversarial B1
Kind: L
Fidelity: exact
Hyps: (a) `0 < ν(O_d)` -/
theorem strictState_calibratedRefinement_pushdown (d : ι) (hO : 0 < nu C B (obs d)) :
    (condOn (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves)
        ((mass_runPMF_pos_iff C B _).mpr hO)).map (world B) =
      toPMF (calibratedState C B (obs d) hO).P := by
  have hq : 0 < probOf (leafDistr C B) (worldEv B (obs d)) := by
    rw [probOf_leafDistr]; exact hO
  show (condOn (toPMF (leafDistr C B)) _ _).map _ = _
  rw [condOn_toPMF' _ _ hq ((mass_runPMF_pos_iff C B _).mpr hO), toPMF_map_world,
    pushdownDistr_condDistr_worldEv C B (obs d) hO hq]

/-- **The anticipation structure is idle in Def 6.2's refinement clause**: for any positive event
`S`, the conditioning on `S` is a calibrated-refinement posterior for one structure iff for any
other — in SC's formalization the "admitted atoms" `Aplus` are a free field of the structure, not
a constraint on the posterior. This is why `OccOnlyPosterior` restricts to the occurrence atoms
in the predicate (`aplus := evAtom (occ d B)`), not through the structure.
Source: `anticipation.md` AN-9 ("with `Ā⁺ = Ā_occ`"); audit r2 adversarial B1, N5
Kind: L
Fidelity: n/a -/
theorem calibratedRefinement_as_idle (S : Set B.Leaves) (hS : 0 < mass (runPMF C B) S)
    (as as' : AnticipationStructure (runPMF C B) B.Leaves) :
    Nonempty (CalibratedRefinement (runPMF C B) (condOn (runPMF C B) S hS) as) ↔
      Nonempty (CalibratedRefinement (runPMF C B) (condOn (runPMF C B) S hS) as') := by
  rw [refinement_posteriors_eq_condOn, refinement_posteriors_eq_condOn]

end sc

/-! ## T7: calibrated refinement's verdict (AN-9) and AN-10 -/

section refinement

variable (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)

/-- **A refinement by the occurrence atoms of `d` alone**: the posterior is the run law
conditioned on an event of the two-atom algebra `{occ(d), occ(d)ᶜ}` — Def 6.2's posterior
clause with `aplus := evAtom (occ d B)`. Two disclosures. (i) The restriction lives in this
predicate, not in SC's structure: `CalibratedRefinement P P' as` is nonempty for every `as`
whenever `P'` is any event conditioning (`calibratedRefinement_as_idle`), so AN-9's "with
`Ā⁺ = Ā_occ`" is not a constraint SC's object can express; rendering it as the `hpost` clause is
the right rendering (no weaker object is substituted), imposed by hand. (ii) The algebra is one
point's: the sub-algebra of AN-6's joint `Ā_occ` (atoms `ā_S` indexed by sets of points) generated
by `T_d = {S : d ∈ S}` — the mandate's `Aplus = Bool`. It coincides with the joint algebra on
`B₁` (one point) and, on TN-V1 and Told-You-So, at the non-root point (`d_E`'s atoms are
`λ⁻¹O_F`/`λ⁻¹O_E`, `d₁₀`'s the `(5,5)` run and the ten branch), which is why the package's cells
read "the refinement at `d_E` reaches `d_F`'s strict state" where AN-9 says "at `d_F`, via
`d_E`'s non-consultation" — same event, same posterior, the point relabelled (audit r2 fidelity
N1).
Source: `anticipation.md` AN-9 ("with `Ā⁺ = Ā_occ` and any event"); AN-6 (`Ā_occ`)
Kind: D
Fidelity: variant: one point's occurrence atoms (the mandate's `Aplus = Bool`), the sub-algebra
of AN-6's joint `Ā_occ` generated by `T_d`; the restriction imposed in the predicate -/
def OccOnlyPosterior (P' : PMF B.Leaves) : Prop :=
  ∃ (ev : Set Bool) (hpos : 0 < mass (runPMF C B) (evAtom (occ d B) ⁻¹' ev)),
    P' = condOn (runPMF C B) (evAtom (occ d B) ⁻¹' ev) hpos

/-- **AN-9, the occurrence-only refinement is too coarse**: its posteriors are `μ(· | occ(d))`,
`μ(· | occ(d)ᶜ)` or `μ` itself — on `mug1` (`occ = ⊤`) only `μ`, so the tails-certain state is
not reached (`mug1_occOnly_not_tailsCertain`, `WitnessesPermissive.lean`); admitting the
observation event `λ⁻¹O_d` reaches every strict-OC state (`strictState_calibratedRefinement`,
pushdown `strictState_calibratedRefinement_pushdown`), so Def 6.2's verdict is a choice of
admitted events — a choice SC's structure does not record (`calibratedRefinement_as_idle`; the
`OccOnlyPosterior` docstring). The proof is a four-way case split on `ev ⊆ Bool` (`∅` excluded
by `hpos`), hence L.
Source: `anticipation.md` AN-9 ("on `B₁` the only posterior is `ν` (one atom) — the
tails-certain state fails")
Kind: L
Fidelity: variant: one point's occurrence atoms (see `OccOnlyPosterior`)
Hyps: none -/
theorem occOnly_posteriors (P' : PMF B.Leaves) (h : OccOnlyPosterior C B d P') :
    (∃ hpos, P' = condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) hpos) ∨
    (∃ hpos, P' = condOn (runPMF C B) (↑(occ d B) : Set B.Leaves)ᶜ hpos) ∨
    P' = runPMF C B := by
  obtain ⟨ev, hpos, hP'⟩ := h
  have htrue : evAtom (occ d B) ⁻¹' {true} = (↑(occ d B) : Set B.Leaves) :=
    evAtom_preimage_true _
  have hfalse : evAtom (occ d B) ⁻¹' {false} = (↑(occ d B) : Set B.Leaves)ᶜ := by
    ext ℓ; simp [evAtom]
  by_cases ht : true ∈ ev <;> by_cases hf : false ∈ ev
  · have hu : ev = Set.univ := by
      ext b; cases b <;> simp [ht, hf]
    right; right
    have : evAtom (occ d B) ⁻¹' ev = Set.univ := by rw [hu, Set.preimage_univ]
    rw [hP', condOn_congr _ this hpos]
    exact condOn_univ _ _
  · have hu : ev = {true} := by
      ext b; cases b <;> simp [ht, hf]
    left
    have : evAtom (occ d B) ⁻¹' ev = (↑(occ d B) : Set B.Leaves) := by rw [hu, htrue]
    exact ⟨this ▸ hpos, hP'.trans (condOn_congr _ this hpos)⟩
  · have hu : ev = {false} := by
      ext b; cases b <;> simp [ht, hf]
    right; left
    have : evAtom (occ d B) ⁻¹' ev = (↑(occ d B) : Set B.Leaves)ᶜ := by rw [hu, hfalse]
    exact ⟨this ▸ hpos, hP'.trans (condOn_congr _ this hpos)⟩
  · exfalso
    have hu : ev = ∅ := by
      ext b; cases b <;> simp [ht, hf]
    rw [hu, Set.preimage_empty, mass_empty] at hpos
    exact lt_irrefl 0 hpos

/-- **AN-10, `Ĉ = 𝓔` via `(λ, id)`**: the common information `(Ω, world B, id)` from the run space
to the base carrier.
Source: `anticipation.md` AN-10 ("with `Ĉ = 𝓔` and the occurrence anticipation")
Kind: D -/
abbrev worldCI : CommonInfo B.Leaves Ω := { C := Ω, c := world B, c' := id }

/-- **AN-10, SC Prop 4.7's Level 2′ collapses**: with `Ĉ = 𝓔` the range condition of
`commonInfo_condModel_iff` is automatic (`c' = id` is surjective) and a `Ĉ`-compatible model from
the run law to a state `s` exists iff `P_s ≪ ν` — everything beyond absolute continuity comes from
fixing the evidence.
Source: `anticipation.md` AN-10 ("both D–Z conditions read `P_s ≪ ν`")
Kind: C
Fidelity: exact (finite carrier)
Hyps: none -/
theorem an10_compatible_iff_ac (s : State Ω ℚ) :
    (∃ m : CondModel (runPMF C B) (toPMF s.P), Compatible m (worldCI B)) ↔
      ∀ ω, nu C B {ω} = 0 → s.P.w ω = 0 := by
  rw [commonInfo_condModel_iff]
  have hC₁ : (worldCI B).C₁ (runPMF C B) = toPMF (priorState C B).P := by
    show (runPMF C B).map (world B) = _
    rw [runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P]
  have hC₂ : (worldCI B).C₂ (toPMF s.P) = toPMF s.P := PMF.map_id _
  rw [hC₁, hC₂, boundedDensity_iff_of_fintype, toPMF_ac_iff]
  have hp : ∀ ω, (priorState C B).P.w ω = nu C B {ω} := by
    intro ω
    have := priorState_pr C B {ω}
    simp only [State.pr, probOf_singleton] at this
    exact this
  simp only [hp]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun y _ => ⟨y, rfl⟩⟩

end refinement

end Cleanroom.Decision.DpFirstpersonSc
