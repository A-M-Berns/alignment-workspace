import Cleanroom.Udt.UdtPaperTiling.Theorem1

/-!
# `udt-paper-tiling` · Coordination: Policy Coordination, Theorem 2, and the coordination zoo
(T7, T8, T9 — the abstract part; the finite models are in `CoordinationWitness.lean`)

* `PolicyCoordination` (`main.tex` 175–180): a well-typed policy of positive mass at least as good
  as `πstar` overall has, at every observation, a chosen-point value at least `πstar`'s (positivity
  guards on the point events). **Theorem 2** (`thm2_udt10_tiling`) in the form the paper's proof
  supports (bli-paper-007's flag: the proof needs `π*(o) = aₘ`): under Policy Fairness and Policy
  Coordination, at every observation the fixed point's own action is at most as good as the
  available non-modifying action `eff πstar o`. The paper's phrasing, "UDT 1.0 does not strictly
  prefer any self-modifying action", is the corollary `thm2_no_strict_selfMod`, which is where the
  UDT 1.0 rule (`IsUDT10`) enters. Kind L (two applications of two hypotheses; audit r1); the
  docstring says what bli-slides-027 says: coordination plays too large a role. `udt-bli-tiling`
  imports these names for bli-paper-006/007. **The package forces a tie** (`thm2_forced_tie`,
  audit r1): with the rule, the `≤` at `eff πstar o` is `=` at every observation, so every
  witness of `thm2_no_strict_selfMod`'s package ties at the modifying points — that is the
  content of the hypotheses, not a degeneracy. Witnesses: `Theorem2Witness.lean` (`Thm2Wit`, the
  fixed-point form with PC firing and a strict conclusion; `Thm2Tie`, the full package with the
  rule, non-degenerate up to the forced tie).
* **The squeeze made exact** (T9, bli-paper-071/072): the proof uses Policy Coordination only at
  `π = eff πstar`, with the *equality* antecedent Policy Fairness supplies; `PCAtEff` is that one
  instance and is the conclusion's witness form (`thm2_of_pcAtEff`, Kind S). Any coordination
  assumption that fires at `eff πstar` is this squeeze — Abram's "abuses PC to switch between
  global optima" (l3 b.24–25). `StrictPolicyCoordination` never fires there (`strictPC_of_isUDT11`:
  it is vacuous at any UDT 1.1 optimum), and Theorem 2 is **false** under it
  (`CoordinationWitness.lean`).
* **Mix-and-match** (T8(a), bli-paper-071): PC with the UDT 1.0 rule makes equally good policies
  pointwise equal (`pc_mix_and_match`), so any pointwise recombination of two global optima is a
  UDT 1.0 fixed point (`isUDT10_recombination`) — the source's "far too strong".
* **The restricted variants** (T8(c), bli-paper-073): the antecedent over `Π^{-m}` still proves
  Theorem 2 (`thm2_of_pcNonMod`); the consequent at non-modifying points only
  (`PolicyCoordinationAtNonMod`) and the comparison against `eff πstar` (`PolicyCoordinationEff`)
  do not (`CoordinationWitness.lean`).
* **Tie-handling PC** (T8(d), bli-paper-019(ii)): inconsistent with `π = πstar`
  (`tiePC_self_inconsistent`) and, under PF, with any fixed point whose effective policy agrees
  with it somewhere (`tiePC_eff_inconsistent`). ATTRIBUTION-UNVETTED reading of l3 b.33–38, where
  Abram already doubts it.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}
variable (S : PaperStructure 𝒟 Act) (Λ : PaperLayer P)

/-! ## The assumptions -/

/-- **Policy Coordination**: for every well-typed policy `π` of positive mass, if `π` is at least
as good as `πstar` overall then at every observation (with both point events positive) the
chosen-point value of `π o` is at least that of `πstar o`.
Source: `main.tex` 175–180 (bli-paper-006); bli-slides-027
Kind: D
Fidelity: variant: positivity guards on the policy and the two point events -/
def PolicyCoordination (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU πstar ≤ Λ.procEU π →
    ∀ o, 0 < Λ.pointMass o (πstar o) → 0 < Λ.pointMass o (π o) →
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o (π o)

/-- **Strict Policy Coordination**: Policy Coordination with `<` in the antecedent (Abram's first
proposal, l3 b.26–29).
Source: [[udt-tiling-working-notes-2025-06-30]] l3 b.26–29 (bli-paper-019(i), 072)
Kind: D
Fidelity: exact (same guards) -/
def StrictPolicyCoordination (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU πstar < Λ.procEU π →
    ∀ o, 0 < Λ.pointMass o (πstar o) → 0 < Λ.pointMass o (π o) →
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o (π o)

/-- **Policy Coordination restricted to non-modifying `π`** (073's first variant).
Source: [[udt-tiling-working-notes-2025-06-30]] l3 b.40–42 (bli-paper-073)
Kind: D
Fidelity: exact (same guards) -/
def PolicyCoordinationNonMod (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → S.NonMod π → 0 < Λ.procMass π → Λ.procEU πstar ≤ Λ.procEU π →
    ∀ o, 0 < Λ.pointMass o (πstar o) → 0 < Λ.pointMass o (π o) →
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o (π o)

/-- **Policy Coordination with the consequent only at non-modifying points of `πstar`** (073's
second variant).
Source: bli-paper-073
Kind: D
Fidelity: exact (same guards) -/
def PolicyCoordinationAtNonMod (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU πstar ≤ Λ.procEU π →
    ∀ o, πstar o ∉ S.selfMod → 0 < Λ.pointMass o (πstar o) → 0 < Λ.pointMass o (π o) →
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o (π o)

/-- **Policy Coordination compared against `eff πstar`** (073's third variant): both sides of the
assumption read `eff πstar` in place of `πstar`.
Source: bli-paper-073
Kind: D
Fidelity: exact (same guards) -/
def PolicyCoordinationEff (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU (Λ.eff πstar) ≤ Λ.procEU π →
    ∀ o, 0 < Λ.pointMass o (Λ.eff πstar o) → 0 < Λ.pointMass o (π o) →
      Λ.chosenEU o (Λ.eff πstar o) ≤ Λ.chosenEU o (π o)

/-- **Policy Coordination at `eff πstar` only**: the one instance Theorem 2's proof uses, and the
conclusion's witness form. Any coordination assumption that fires at `eff πstar` is this.
Source: bli-paper-071, 072 (the squeeze made exact); `main.tex` 189–197
Kind: D
Fidelity: n/a (the squeeze) -/
def PCAtEff (πstar : Policy 𝒟 Act) : Prop :=
  ∀ o, Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o (Λ.eff πstar o)

/-- **Tie-handling Policy Coordination** (Abram's l3 b.33–37): a well-typed positive policy exactly
as good as `πstar` is pointwise strictly better everywhere or strictly worse everywhere.
Source: [[udt-tiling-working-notes-2025-06-30]] l3 b.33–37 (bli-paper-019(ii));
ATTRIBUTION-UNVETTED reading
Kind: D
Fidelity: exact -/
def TiePolicyCoordination (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU π = Λ.procEU πstar →
    (∀ o, Λ.chosenEU o (πstar o) < Λ.chosenEU o (π o)) ∨
    (∀ o, Λ.chosenEU o (π o) < Λ.chosenEU o (πstar o))

/-! ## Theorem 2 -/

/-- **Policy Fairness + Policy Coordination give PC at `eff πstar`** (the paper's two steps).
Source: `main.tex` 189–197
Kind: C
Fidelity: exact
Hyps: (a) `PolicyFair`, `PolicyCoordination`, positivities; `hidem`/`hwt` (a) from the causal
construction or (c) from a bare `EffData` -/
theorem pcAtEff_of_pc {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hPC : PolicyCoordination S Λ πstar) (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar)
    (hwt : S.WellTyped (Λ.eff πstar)) (hstar : 0 < Λ.procMass πstar)
    (heff : 0 < Λ.procMass (Λ.eff πstar)) : PCAtEff Λ πstar := by
  intro o
  have heq := thm1_udt11_tiling Λ hF πstar hidem hstar heff
  exact hPC (Λ.eff πstar) hwt heff (le_of_eq heq) o
    (Λ.pointMass_pos_of_procMass_pos hstar o) (Λ.pointMass_pos_of_procMass_pos heff o)

/-- **Theorem 2 from PC at `eff πstar`** — the squeeze: the conclusion is the hypothesis with the
witness `eff πstar o` named. Kind S, recorded so that the role of coordination is visible.
Source: bli-paper-071, 072; `main.tex` 185–199
Kind: S
Fidelity: exact
Hyps: (a) `PCAtEff`; `hnm`, `hwt` as above; `heff` -/
theorem thm2_of_pcAtEff {πstar : Policy 𝒟 Act} (h : PCAtEff Λ πstar)
    (hnm : S.NonMod (Λ.eff πstar)) (hwt : S.WellTyped (Λ.eff πstar))
    (heff : 0 < Λ.procMass (Λ.eff πstar)) :
    ∀ o, ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < Λ.pointMass o a ∧
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o a :=
  fun o => ⟨Λ.eff πstar o, hwt o, hnm o, Λ.pointMass_pos_of_procMass_pos heff o, h o⟩

/-- **Theorem 2 (UDT 1.0 tiling under Policy Fairness and Policy Coordination), fixed-point
form.** For the chosen policy `πstar` of positive mass whose effective policy has positive mass:
at every observation there is an available non-modifying action of positive point mass (namely
`eff πstar o`) at least as good as `πstar o`. The paper's proof: fairness gives
`𝔼[U | π* = eff πstar] = 𝔼[U | π* = πstar]`, coordination turns it into the pointwise inequality.
"Coordination plays too large a role" (bli-slides-027, `main.tex` 201): trust is assumed, not
derived — see `thm2_of_pcAtEff` for the exact squeeze. The UDT 1.0 rule is not used here; it
enters only in the corollary `thm2_no_strict_selfMod` (bli-paper-007's flag). The body is
`thm2_of_pcAtEff ∘ pcAtEff_of_pc`: Theorem 1 (one application of PF) and one application of PC
at `eff πstar` — Kind L, not C (audit r1).
Source: `main.tex` 185–199, Theorem 2 (bli-paper-007); bli-slides-027
Kind: L
Fidelity: variant: the fixed-point form the proof supports; positivity explicit
Hyps: (a) `PolicyFair`, `PolicyCoordination`, positivities; `hidem`/`hnm`/`hwt` (a) from the
causal construction, (c) from a bare `EffData` -/
theorem thm2_udt10_tiling {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hPC : PolicyCoordination S Λ πstar) (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar)
    (hnm : S.NonMod (Λ.eff πstar)) (hwt : S.WellTyped (Λ.eff πstar))
    (hstar : 0 < Λ.procMass πstar) (heff : 0 < Λ.procMass (Λ.eff πstar)) :
    ∀ o, ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < Λ.pointMass o a ∧
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o a :=
  thm2_of_pcAtEff S Λ (pcAtEff_of_pc S Λ hF hPC hidem hwt hstar heff) hnm hwt heff

/-- **Theorem 2 in the paper's words**: with `πstar` a UDT 1.0 fixed point, no available
self-modifying action of positive point mass is strictly better than every available
non-modifying action of positive point mass. (If `aₘ` were, then `πstar o`, which is at least as
good as `aₘ`, would be too — contradicting the non-modifying `a` of `thm2_udt10_tiling`.)
The hypothesis `aₘ ∈ 𝒜^m` is **not used** by the proof: the statement holds for every available
positive action `aₘ`, self-modifying or not (audit r1); it is kept so that the statement reads
as the paper's sentence.
Source: `main.tex` 185–199, Theorem 2 (bli-paper-007)
Kind: L
Fidelity: exact (positive points only); the self-modification restriction is inert
Hyps: as `thm2_udt10_tiling`, plus (a) `IsUDT10` -/
theorem thm2_no_strict_selfMod {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hPC : PolicyCoordination S Λ πstar) (hU : IsUDT10 S Λ πstar)
    (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar) (hnm : S.NonMod (Λ.eff πstar))
    (hwt : S.WellTyped (Λ.eff πstar)) (hstar : 0 < Λ.procMass πstar)
    (heff : 0 < Λ.procMass (Λ.eff πstar)) :
    ¬ ∃ o, ∃ aₘ ∈ S.Aof o, aₘ ∈ S.selfMod ∧ 0 < Λ.pointMass o aₘ ∧
      ∀ a ∈ S.Aof o, a ∉ S.selfMod → 0 < Λ.pointMass o a → Λ.chosenEU o a < Λ.chosenEU o aₘ := by
  rintro ⟨o, aₘ, haₘ, _, hpos, hstrict⟩
  obtain ⟨a, ha, hanm, hapos, hle⟩ := thm2_udt10_tiling S Λ hF hPC hidem hnm hwt hstar heff o
  have h1 := hstrict a ha hanm hapos
  have h2 := (hU o).2 aₘ haₘ hpos
  linarith

/-- **Theorem 2's full package forces a tie at every observation**: under Policy Fairness, Policy
Coordination, the UDT 1.0 fixed point and the positivities, the `≤` of Theorem 2's conclusion at
the witness `eff πstar o` is an equality — PC at `eff πstar` one way (`pcAtEff_of_pc`), the fixed
point the other. So every witness of `thm2_no_strict_selfMod`'s package is a "tie model" at the
modifying points: that is the content of the hypotheses (the sharpest form of F-5's squeeze
finding), not a degeneracy of any particular model. `Theorem2Witness.lean` exhibits it.
Source: audit r1 (fidelity) probe `Thm2Package`; `main.tex` 185–199 with the UDT 1.0 rule
Kind: L
Fidelity: n/a (a consequence of the hypothesis package, not a claim of the paper: Theorem 2
compares `aₘ` with the non-modifying actions, and never `π*(o)` with `eff π*(o)`)
Hyps: as `thm2_no_strict_selfMod` -/
theorem thm2_forced_tie {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hPC : PolicyCoordination S Λ πstar) (hU : IsUDT10 S Λ πstar)
    (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar) (hwt : S.WellTyped (Λ.eff πstar))
    (hstar : 0 < Λ.procMass πstar) (heff : 0 < Λ.procMass (Λ.eff πstar)) :
    ∀ o, Λ.chosenEU o (πstar o) = Λ.chosenEU o (Λ.eff πstar o) := by
  intro o
  apply le_antisymm
  · exact pcAtEff_of_pc S Λ hF hPC hidem hwt hstar heff o
  · exact (hU o).2 (Λ.eff πstar o) (hwt o) (Λ.pointMass_pos_of_procMass_pos heff o)

/-- **The non-modifying antecedent suffices** (073's first variant still proves Theorem 2,
because the proof only applies coordination to `eff πstar ∈ Π^{-m}` — Abram's "still too strong").
Kind L (regraded from C in repair round 2): the body is `thm2_udt10_tiling`'s with
`PolicyCoordinationNonMod` in place of `PolicyCoordination`.
Source: bli-paper-073; [[udt-tiling-working-notes-2025-06-30]] l3 b.40–42
Kind: L
Fidelity: exact
Hyps: as `thm2_udt10_tiling` with `PolicyCoordinationNonMod` -/
theorem thm2_of_pcNonMod {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hPC : PolicyCoordinationNonMod S Λ πstar) (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar)
    (hnm : S.NonMod (Λ.eff πstar)) (hwt : S.WellTyped (Λ.eff πstar))
    (hstar : 0 < Λ.procMass πstar) (heff : 0 < Λ.procMass (Λ.eff πstar)) :
    ∀ o, ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < Λ.pointMass o a ∧
      Λ.chosenEU o (πstar o) ≤ Λ.chosenEU o a := by
  have h : PCAtEff Λ πstar := by
    intro o
    have heq := thm1_udt11_tiling Λ hF πstar hidem hstar heff
    exact hPC (Λ.eff πstar) hwt hnm heff (le_of_eq heq) o
      (Λ.pointMass_pos_of_procMass_pos hstar o) (Λ.pointMass_pos_of_procMass_pos heff o)
  exact thm2_of_pcAtEff S Λ h hnm hwt heff

/-! ## Mix-and-match -/

/-- **Mix-and-match** (bli-paper-071, 006's flag): with Policy Coordination and the UDT 1.0 rule,
a well-typed positive policy exactly as good as `πstar` has pointwise equal chosen-point values.
Source: [[udt-tiling-working-notes-2025-06-30]] l3 b.30 ("if there are two equally good policies,
we can mix-and-match policy-points from those policies. This is far too strong")
Kind: L
Fidelity: exact
Hyps: (a) `PolicyCoordination`, `IsUDT10`, positivities -/
theorem pc_mix_and_match {πstar : Policy 𝒟 Act} (hPC : PolicyCoordination S Λ πstar)
    (hU : IsUDT10 S Λ πstar) (hstar : 0 < Λ.procMass πstar) (π : Policy 𝒟 Act)
    (hπ : S.WellTyped π) (hpos : 0 < Λ.procMass π) (heq : Λ.procEU π = Λ.procEU πstar) :
    ∀ o, Λ.chosenEU o (π o) = Λ.chosenEU o (πstar o) := by
  intro o
  apply le_antisymm
  · exact (hU o).2 (π o) (hπ o) (Λ.pointMass_pos_of_procMass_pos hpos o)
  · exact hPC π hπ hpos (le_of_eq heq.symm) o (Λ.pointMass_pos_of_procMass_pos hstar o)
      (Λ.pointMass_pos_of_procMass_pos hpos o)

/-- **Any pointwise recombination of two global optima is a UDT 1.0 fixed point** under Policy
Coordination: the "mix-and-match" consequence made explicit.
Source: bli-paper-071
Kind: L
Fidelity: exact
Hyps: as `pc_mix_and_match` -/
theorem isUDT10_recombination {πstar : Policy 𝒟 Act} (hPC : PolicyCoordination S Λ πstar)
    (hU : IsUDT10 S Λ πstar) (hstar : 0 < Λ.procMass πstar) (π : Policy 𝒟 Act)
    (hπ : S.WellTyped π) (hpos : 0 < Λ.procMass π) (heq : Λ.procEU π = Λ.procEU πstar)
    (π' : Policy 𝒟 Act) (hπ' : ∀ o, π' o = π o ∨ π' o = πstar o) : IsUDT10 S Λ π' := by
  intro o
  have hval : Λ.chosenEU o (π' o) = Λ.chosenEU o (πstar o) := by
    rcases hπ' o with h | h
    · rw [h]; exact pc_mix_and_match S Λ hPC hU hstar π hπ hpos heq o
    · rw [h]
  refine ⟨?_, fun a ha hapos => ?_⟩
  · rcases hπ' o with h | h
    · rw [h]; exact hπ o
    · rw [h]; exact (hU o).1
  · rw [hval]; exact (hU o).2 a ha hapos

/-! ## Strict PC is vacuous at an optimum; tie-handling PC is inconsistent -/

/-- **Strict Policy Coordination holds vacuously at any UDT 1.1 optimum**: no well-typed positive
policy is strictly better. So it can never fire at `eff πstar` and cannot replace Policy
Coordination in Theorem 2 (the countermodel is in `CoordinationWitness.lean`).
Source: bli-paper-072 ("the paper's proof uses PF's equality, which strict PC does not fire on")
Kind: L
Fidelity: exact
Hyps: (a) `IsUDT11` -/
theorem strictPC_of_isUDT11 {πstar : Policy 𝒟 Act} (hU : IsUDT11 S Λ πstar) :
    StrictPolicyCoordination S Λ πstar := by
  intro π hπ hpos hlt
  exact absurd (hU π hπ hpos) (not_le.mpr hlt)

/-- **Tie-handling PC is inconsistent with `π = πstar`**: applied to `πstar` itself it demands
`chosenEU o (πstar o) < chosenEU o (πstar o)`. This is the trivial half, formalizing b.33–37
literally including `π = π*`, which b.38 already withdraws; the substantive statement is
`tiePC_eff_inconsistent`, which survives any `π ≠ π*` restriction (for a self-modifying fixed
point `eff πstar ≠ πstar`).
Source: bli-paper-019(ii); [[udt-tiling-working-notes-2025-06-30]] l3 b.38 (Abram's own doubt)
Kind: L
Fidelity: exact
Hyps: (a) `TiePolicyCoordination`, `πstar` well-typed and positive, an observation exists -/
theorem tiePC_self_inconsistent [Nonempty ↥𝒟] {πstar : Policy 𝒟 Act}
    (hT : TiePolicyCoordination S Λ πstar) (hwt : S.WellTyped πstar)
    (hstar : 0 < Λ.procMass πstar) : False := by
  obtain ⟨o⟩ := ‹Nonempty ↥𝒟›
  rcases hT πstar hwt hstar rfl with h | h
  · exact lt_irrefl _ (h o)
  · exact lt_irrefl _ (h o)

/-- **Tie-handling PC is inconsistent, under Policy Fairness, with any fixed point whose effective
policy agrees with it somewhere**: `eff πstar` is exactly as good as `πstar`, so tie-PC demands a
strict pointwise inequality everywhere, which fails where the two agree.
Source: bli-paper-019(ii)
Kind: L
Fidelity: exact
Hyps: (a) `PolicyFair`, `TiePolicyCoordination`, positivities, agreement at `o₀`; `hidem`/`hwt`
as above -/
theorem tiePC_eff_inconsistent {πstar : Policy 𝒟 Act} (hF : P.PolicyFair Λ.toProcLayer)
    (hT : TiePolicyCoordination S Λ πstar) (hidem : Λ.eff (Λ.eff πstar) = Λ.eff πstar)
    (hwt : S.WellTyped (Λ.eff πstar)) (hstar : 0 < Λ.procMass πstar)
    (heff : 0 < Λ.procMass (Λ.eff πstar)) (o₀ : ↥𝒟) (hagree : Λ.eff πstar o₀ = πstar o₀) :
    False := by
  have heq := thm1_udt11_tiling Λ hF πstar hidem hstar heff
  rcases hT (Λ.eff πstar) hwt heff heq.symm with h | h
  · have := h o₀; rw [hagree] at this; exact lt_irrefl _ this
  · have := h o₀; rw [hagree] at this; exact lt_irrefl _ this

end Cleanroom.Udt.UdtPaperTiling
