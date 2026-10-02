import Cleanroom.Bli.UdtBliCore.Defs

/-!
# `udt-paper-tiling` · Structure: the paper's policy formalism, `elim`, and `eff` (T1)

The Understanding Trust paper (`main.tex` 77–97) fixes observations `𝒪`, actions `𝒜` with the
available actions `𝒜_o ⊆ 𝒜` at each observation, self-modifying actions `𝒜^m`, the outwardly
identical non-modifying twin `â` of each `a ∈ 𝒜^m`, and the set `mod(a)` of policy-points a
self-modifying action forces. Policies are `Policy 𝒟 Act := ↥𝒟 → Act` from `udt-bli-core`
(observations are the day-`m` tables `↥𝒟`, written `o` in prose); the paper's typing is data on a
`PaperStructure`, well-typedness is a predicate (`variant: policies are total functions`).

* `PaperStructure`: `Aof` (`𝒜_o`), `selfMod` (`𝒜^m`), `twin` (`â`), `mod` (`mod(a)` as a partial
  function `↥𝒟 → Option Act`: the paper's set of policy-points, functional by representation).
* `WellTyped`, `NonMod` (`Π`, `Π^{-m}`), `elim` (`main.tex` 90–94).
* `EffData`: the paper's `eff` taken as the paper takes it — assumed to exist, non-modifying and
  idempotent (`main.tex` 97). Grade **(c)** wherever a theorem uses one.
* `CausalStructure` and `effCausal`: the construction of record (bli-paper-062, bli-slides-036):
  a rank on observations under which modifications target strictly later observations, no two
  modifications disagree on a point, and forced actions are non-modifying and well-typed. `fires`
  (a self-modification at `o` takes effect unless an earlier firing modification overrides `o`)
  is defined by well-founded recursion on the rank; `effCausal` is non-modifying, idempotent and
  type-preserving **as theorems** (`effCausal_nonMod`, `effCausal_idem`, `effCausal_wellTyped`),
  so `EffData.ofCausal` turns the paper's assumption into grade (a).
* `effCausal_fires_at_null`: `eff` is a function of the policy alone, so a modification issued
  at a null-mass observation still rewrites (bli-slides-009's third race condition, as a finding).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30), namespace
`Cleanroom.Udt.UdtPaperTiling`.
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act]

/-- **The paper's action structure** over the observations `↥𝒟` and the actions `Act`: the
available actions `Aof o` (`𝒜_o`), the self-modifying actions `selfMod` (`𝒜^m`), the
non-modifying twin `twin a` (`â`: not self-modifying, available exactly where `a` is, the
identity on non-modifying actions), and `mod a o'` — `some a'` iff `(o', a') ∈ mod(a)`, so the
paper's set of forced policy-points is a partial function (functional by representation) and a
non-modifying action forces nothing. Disjointness of the `Aof o` (`main.tex:79`) is a hypothesis
where a proof needs it, not a field.
Source: `main.tex` 77–89 (bli-paper-001)
Kind: D
Fidelity: variant: policies are total functions with well-typedness a predicate; `mod(a)` is a
partial function `↥𝒟 → Option Act` -/
structure PaperStructure (𝒟 : Finset (Table 𝒮 m)) (Act : Type) [Fintype Act] [DecidableEq Act]
    where
  /-- The actions available at `o` (`𝒜_o`). -/
  Aof : ↥𝒟 → Finset Act
  /-- The self-modifying actions (`𝒜^m`). -/
  selfMod : Finset Act
  /-- The outwardly identical non-modifying version `â` of `a`. -/
  twin : Act → Act
  /-- `â ∈ 𝒜^{-m}`. -/
  twin_nonMod : ∀ a, twin a ∉ selfMod
  /-- `â` is available wherever `a` is (the paper's "appears identical from the outside"; with
  the paper's disjoint action sets the converse follows, and it is not needed). -/
  twin_typed : ∀ a o, a ∈ Aof o → twin a ∈ Aof o
  /-- On non-modifying actions the twin is the action itself. -/
  twin_id : ∀ a, a ∉ selfMod → twin a = a
  /-- The policy-points forced by `a`: `mod a o' = some a'` iff `(o', a') ∈ mod(a)`. -/
  mod : Act → ↥𝒟 → Option Act
  /-- A non-modifying action forces nothing. -/
  mod_nonMod_none : ∀ a, a ∉ selfMod → ∀ o', mod a o' = none

namespace PaperStructure

variable (S : PaperStructure 𝒟 Act)

/-- **Well-typed policy** (the paper's `Π`): `π o ∈ 𝒜_o` at every observation.
Source: `main.tex` 79 (bli-paper-001)
Kind: D
Fidelity: exact -/
def WellTyped (π : Policy 𝒟 Act) : Prop := ∀ o, π o ∈ S.Aof o

/-- **Non-modifying policy** (the paper's `Π^{-m}`): no self-modifying action anywhere.
Source: `main.tex` 83 (bli-paper-001)
Kind: D
Fidelity: exact -/
def NonMod (π : Policy 𝒟 Act) : Prop := ∀ o, π o ∉ S.selfMod

/-- The available actions are pairwise disjoint across observations (`main.tex:79`), as a
hypothesis.
Source: `main.tex` 79 (bli-paper-001)
Kind: D
Fidelity: exact -/
def DisjointActions : Prop := ∀ o₁ o₂, o₁ ≠ o₂ → Disjoint (S.Aof o₁) (S.Aof o₂)

/-- The non-modifying actions available at `o`: `𝒜^{-m} ∩ 𝒜_o`. This is the set Theorem 3's
maximum ranges over here (the paper writes `𝒜^{-m}`, which includes unavailable actions —
bli-paper-013(ii)).
Source: `main.tex` 83, 245 (bli-paper-013)
Kind: D
Fidelity: stronger: intersected with `𝒜_o` -/
def nonModAt (o : ↥𝒟) : Finset Act := (S.Aof o).filter (fun a => a ∉ S.selfMod)

/-- Supporting lemma `mem_nonModAt` (infrastructure).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mem_nonModAt (o : ↥𝒟) (a : Act) : a ∈ S.nonModAt o ↔ a ∈ S.Aof o ∧ a ∉ S.selfMod := by
  simp [nonModAt]

/-- **`elim(π, o, a)`**: eliminate the self-modifying point `π(o) = a` — `â` at `o`, the forced
action at every point of `mod(a)`, `π` elsewhere.
Source: `main.tex` 90–94 (bli-paper-001)
Kind: D
Fidelity: exact -/
def elim (π : Policy 𝒟 Act) (o : ↥𝒟) (a : Act) : Policy 𝒟 Act := fun o' =>
  if o' = o then S.twin a else
    match S.mod a o' with
    | some a' => a'
    | none => π o'

/-- `elim` at the eliminated point is the twin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma elim_self (π : Policy 𝒟 Act) (o : ↥𝒟) (a : Act) : S.elim π o a o = S.twin a := by
  simp [elim]

/-- `elim` at a forced point is the forced action.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma elim_forced (π : Policy 𝒟 Act) {o o' : ↥𝒟} (a a' : Act) (hne : o' ≠ o)
    (h : S.mod a o' = some a') : S.elim π o a o' = a' := by
  simp [elim, hne, h]

/-- `elim` elsewhere is `π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma elim_other (π : Policy 𝒟 Act) {o o' : ↥𝒟} (a : Act) (hne : o' ≠ o)
    (h : S.mod a o' = none) : S.elim π o a o' = π o' := by
  simp [elim, hne, h]

/-- **The effective-policy map taken as the paper takes it**: `eff` exists, is uniquely defined,
non-modifying, idempotent and type-preserving (`main.tex` 97: "We need to assume that `eff(π)`
always exists and is uniquely defined … `eff(π) ∈ Π − Π^m`. Importantly, this implies
`eff(π) = eff(eff(π))`"). Every theorem that takes an `EffData` carries these as grade **(c)**
hypotheses (the outward-behaviour equivalence is not expressible); `EffData.ofCausal` discharges
them from the construction of record.
Source: `main.tex` 95–97 (bli-paper-001)
Kind: D
Fidelity: exact (the paper's assumptions as fields) -/
structure EffData where
  /-- The effective policy. -/
  eff : Policy 𝒟 Act → Policy 𝒟 Act
  /-- `eff(π) ∈ Π^{-m}`. -/
  eff_nonMod : ∀ π, S.NonMod (eff π)
  /-- `eff(eff(π)) = eff(π)`. -/
  eff_idem : ∀ π, eff (eff π) = eff π
  /-- `eff` preserves well-typedness (`eff(π) ∈ Π`). -/
  eff_wellTyped : ∀ π, S.WellTyped π → S.WellTyped (eff π)

/-! ## The causal construction of record -/

/-- **A causal structure** on a paper structure: a rank on observations under which every
modification an available action issues targets a strictly later observation (`rank_lt`), no two
modifications disagree on a point (`no_disagree`), forced actions are non-modifying
(`mod_nonMod`) and well-typed (`mod_typed`). These are the three hypotheses under which the
paper's "limit of repeated `elim`" exists and is unique (bli-paper-062's proposal; bli-slides-036's
assumption turned into theorems); each of Paul's race conditions (bli-slides-009) violates one of
them (`StructureWitness.lean`).
Source: bli-paper-062; bli-slides-036; `main.tex` 97 footnote ("These restrictions impose a notion
of time, or causality")
Kind: D
Fidelity: variant: the paper assumes the limit; here the order is explicit data -/
structure CausalStructure where
  /-- The causal rank of an observation. -/
  rank : ↥𝒟 → ℕ
  /-- An action available at `o` only modifies strictly later observations. -/
  rank_lt : ∀ a o o' a', a ∈ S.Aof o → S.mod a o' = some a' → rank o < rank o'
  /-- Two modifications never force one point differently. -/
  no_disagree : ∀ a b o' x y, S.mod a o' = some x → S.mod b o' = some y → x = y
  /-- Forced actions are non-modifying. -/
  mod_nonMod : ∀ a o' a', S.mod a o' = some a' → a' ∉ S.selfMod
  /-- Forced actions are well-typed. -/
  mod_typed : ∀ a o' a', S.mod a o' = some a' → a' ∈ S.Aof o'

namespace CausalStructure

variable {S}
variable (C : S.CausalStructure)

/-- **A self-modification fires**: `π o` is self-modifying and no firing modification at an
observation of strictly lower rank overrides the point `o`. Defined by well-founded recursion on
the rank.
Source: bli-paper-062 (the rank-ordered elimination)
Kind: D
Fidelity: n/a (infrastructure of the construction) -/
def fires (π : Policy 𝒟 Act) (o : ↥𝒟) : Prop :=
  π o ∈ S.selfMod ∧ ∀ o₁, C.rank o₁ < C.rank o → fires π o₁ → S.mod (π o₁) o = none
termination_by C.rank o

/-- The unfolding of `fires`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fires_iff (π : Policy 𝒟 Act) (o : ↥𝒟) :
    C.fires π o ↔ π o ∈ S.selfMod ∧
      ∀ o₁, C.rank o₁ < C.rank o → C.fires π o₁ → S.mod (π o₁) o = none := by
  rw [fires]

/-- A firing point is self-modifying.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fires_selfMod {π : Policy 𝒟 Act} {o : ↥𝒟} (h : C.fires π o) : π o ∈ S.selfMod :=
  ((C.fires_iff π o).mp h).1

/-- The point `o` is **forced** by a firing modification at `o₁`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Forced (π : Policy 𝒟 Act) (o : ↥𝒟) : Prop :=
  ∃ a', ∃ o₁, C.fires π o₁ ∧ S.mod (π o₁) o = some a'

open Classical in
/-- **The effective policy of record** `effCausal π`: at `o`, the action forced by a firing
modification if there is one (unique by `no_disagree`), else the twin of `π o` if `π o` is
self-modifying, else `π o`. Noncomputable only through the classical decision of `Forced`; the
chosen witness is unique (`effCausal_of_forced`), so no junk value enters.
Source: bli-paper-062; bli-slides-036 ("the limit is well defined")
Kind: D
Fidelity: variant: an explicit construction in place of the paper's assumed limit -/
noncomputable def effCausal (π : Policy 𝒟 Act) : Policy 𝒟 Act := fun o =>
  if h : C.Forced π o then Classical.choose h
  else if π o ∈ S.selfMod then S.twin (π o) else π o

/-- The forced action at a forced point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma effCausal_of_forced {π : Policy 𝒟 Act} {o o₁ : ↥𝒟} {a' : Act} (hf : C.fires π o₁)
    (hm : S.mod (π o₁) o = some a') : C.effCausal π o = a' := by
  have h : C.Forced π o := ⟨a', o₁, hf, hm⟩
  unfold effCausal
  rw [dif_pos h]
  obtain ⟨o₂, hf₂, hm₂⟩ := Classical.choose_spec h
  exact C.no_disagree _ _ _ _ _ hm₂ hm

/-- At an unforced point, `effCausal` is the twin or the action itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma effCausal_of_not_forced {π : Policy 𝒟 Act} {o : ↥𝒟} (h : ¬ C.Forced π o) :
    C.effCausal π o = if π o ∈ S.selfMod then S.twin (π o) else π o := by
  unfold effCausal
  rw [dif_neg h]

/-- **`effCausal π` is non-modifying** (`main.tex` 97's `eff(π) ∈ Π^{-m}`, now a theorem).
Source: `main.tex` 97; bli-paper-062
Kind: P
Fidelity: exact
Hyps: (a) none beyond the causal structure -/
theorem effCausal_nonMod (π : Policy 𝒟 Act) : S.NonMod (C.effCausal π) := by
  intro o
  by_cases h : C.Forced π o
  · obtain ⟨a', o₁, hf, hm⟩ := h
    rw [C.effCausal_of_forced hf hm]
    exact C.mod_nonMod _ _ _ hm
  · rw [C.effCausal_of_not_forced h]
    split_ifs with hs
    · exact S.twin_nonMod _
    · exact hs

/-- A non-modifying policy is its own effective policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem effCausal_of_nonMod {π : Policy 𝒟 Act} (h : S.NonMod π) : C.effCausal π = π := by
  funext o
  have hnf : ¬ C.Forced π o := by
    rintro ⟨a', o₁, hf, _⟩
    exact h o₁ (C.fires_selfMod hf)
  rw [C.effCausal_of_not_forced hnf, if_neg (h o)]

/-- **`effCausal` is idempotent** (`main.tex` 97's `eff(π) = eff(eff(π))`, now a theorem).
Source: `main.tex` 97; bli-paper-062
Kind: P
Fidelity: exact
Hyps: (a) none beyond the causal structure -/
theorem effCausal_idem (π : Policy 𝒟 Act) : C.effCausal (C.effCausal π) = C.effCausal π :=
  C.effCausal_of_nonMod (C.effCausal_nonMod π)

/-- **`effCausal` preserves well-typedness**: forced actions are typed (`mod_typed`) and twins
are available where their originals are (`twin_typed`). This is the typing bli-paper-001 flags
as missing from the paper.
Source: `main.tex` 97 (`eff(π) ∈ Π`); bli-paper-001's flag
Kind: P
Fidelity: exact
Hyps: (a) none beyond the causal structure -/
theorem effCausal_wellTyped {π : Policy 𝒟 Act} (h : S.WellTyped π) :
    S.WellTyped (C.effCausal π) := by
  intro o
  by_cases hf : C.Forced π o
  · obtain ⟨a', o₁, hf₁, hm⟩ := hf
    rw [C.effCausal_of_forced hf₁ hm]
    exact C.mod_typed _ _ _ hm
  · rw [C.effCausal_of_not_forced hf]
    split_ifs with hs
    · exact S.twin_typed _ _ (h o)
    · exact h o

/-- **The paper's `eff` from the causal construction**: the three assumed properties of
`main.tex` 97 are the theorems above. A theorem stated over an `EffData` built this way carries
those hypotheses at grade (a).
Source: `main.tex` 97; bli-paper-062
Kind: D
Fidelity: exact -/
noncomputable def toEffData : S.EffData where
  eff := C.effCausal
  eff_nonMod := C.effCausal_nonMod
  eff_idem := C.effCausal_idem
  eff_wellTyped := fun _ h => C.effCausal_wellTyped h

/-- **A modification at a null-mass observation still rewrites.** `effCausal` is a function of
the policy alone: a firing modification at `o₁` forces its target regardless of any prior's mass
at `o₁` — the hypothesis `_hnull` is unused, which is the point. This is bli-slides-009's third
race condition read as a finding about the formalism (an "impossible observation" can still
reprogram the agent, as the working notes also say, l5 b.166), not a defect of the theorems.
Source: bli-slides-009 (race condition 3); [[udt-tiling-working-notes-2025-06-30]] l5 b.166
Kind: L
Fidelity: exact
Hyps: (a) none; the prior-null hypothesis is vacuous by design -/
theorem effCausal_fires_at_null (P : FiniteBLIPrior 𝒮 m 𝒟 Act) {π : Policy 𝒟 Act} {o o₁ : ↥𝒟}
    {a' : Act} (_hnull : P.stateMass o₁ = 0) (hf : C.fires π o₁) (hm : S.mod (π o₁) o = some a') :
    C.effCausal π o = a' :=
  C.effCausal_of_forced hf hm

/-- At an observation of minimal rank among the self-modifying points, `fires` is just
"`π o` is self-modifying": nothing earlier can override it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fires_of_min {π : Policy 𝒟 Act} {o : ↥𝒟} (hs : π o ∈ S.selfMod)
    (hmin : ∀ o₁, C.rank o₁ < C.rank o → π o₁ ∉ S.selfMod) : C.fires π o := by
  rw [C.fires_iff]
  refine ⟨hs, fun o₁ hlt hf => ?_⟩
  exact absurd (C.fires_selfMod hf) (hmin o₁ hlt)

end CausalStructure

end PaperStructure

end Cleanroom.Udt.UdtPaperTiling
