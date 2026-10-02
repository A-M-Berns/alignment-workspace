import Cleanroom.Udt.UdtPaperTiling.Vingean
import Cleanroom.Bli.UdtBliCore.Good

/-!
# `udt-paper-tiling` · Slides: the slides diffed against the paper, and the records (T14, T15)

* **T15(i)** `slides028_restrictedCoord_literal_null`: the literal reading of the AISC talk's
  "Restricted Coordination" (bli-slides-028) conditions on `π*(o) = a₁ ∧ π*(o) = a₂` with
  `a₁ ≠ a₂` — an empty event, so the assumption is about the junk value `0` (the slide is garbled,
  as the inventory says).
* **T15(ii)** `fgf_self_target_null` and `lsm_ob_ne`: without Limited Self-Modification's
  `aₘ ∉ 𝒜_{ob aₘ}`, Fine-Grained Fairness at `o = ob aₘ` would condition on
  `π*(o) = âₘ ∧ π*(o) = ac aₘ`, empty unless `âₘ = ac aₘ`; with it, `o ≠ ob aₘ` whenever `aₘ` is
  available at `o` — bli-slides-045's "can't modify itself" clause, verified as the fix.
* **T15(iii)** Theorem 4 (`thm4_appendixA_tiling`) is bli-slides-045's theorem: a ledger row.
* **T14** `ValueRelevant` and `valueRelevant_iff_good_strict` (bli-paper-2-022's repair): "the
  information is value-relevant" is exactly `udt-bli-core`'s `good_strict_iff` condition — no
  single action is an updateful choice at every table of positive mass — and under its hypotheses
  it is equivalent to the updateful policy strictly beating every constant policy (positive value
  of information is `good`). The UDT twist (conditioning is a policy choice, so the comparison is
  trivial in fair problems) is T13's Version A/B pair.

The assumption-by-assumption table of the slides against the paper is in
`udt-paper-tiling-findings` (F-12).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] (P : FiniteBLIPrior 𝒮 m 𝒟 Act)

/-- **bli-slides-028's Restricted Coordination, read literally, conditions on an empty event**:
`π*(o) = a₁ ∧ π*(o) = a₂` with `a₁ ≠ a₂` has mass `0` and junk value `0`.
Source: bli-slides-028 (AISC 2025 talk p. 17–18); mandate T15(i)
Kind: N−
Fidelity: exact (the literal reading; the inventory calls the slide garbled)
Hyps: (a) `a₁ ≠ a₂` -/
theorem slides028_restrictedCoord_literal_null (o : ↥𝒟) {a₁ a₂ : Act} (h : a₁ ≠ a₂) :
    massOf P.μ (fun ω => P.pp ω o = a₁ ∧ P.pp ω o = a₂) = 0 ∧
    condExp P.μ P.U (fun ω => P.pp ω o = a₁ ∧ P.pp ω o = a₂) = 0 := by
  have hz : massOf P.μ (fun ω => P.pp ω o = a₁ ∧ P.pp ω o = a₂) = 0 := by
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨h₁, h₂⟩
    exact h (h₁.symm.trans h₂)
  refine ⟨hz, ?_⟩
  unfold condExp
  rw [hz, div_zero]

/-- **Without "an action can't modify its own policy-point", Fine-Grained Fairness is about junk**:
at `o = ob aₘ` the fairness cell `π*(o) = âₘ ∧ π*(o) = ac aₘ` is empty unless `âₘ = ac aₘ`.
Source: bli-slides-045 ("can't modify itself"); `main.tex` 205–215; mandate T15(ii)
Kind: N−
Fidelity: exact
Hyps: (a) `twin aₘ ≠ ac aₘ` -/
theorem fgf_self_target_null (S : PaperStructure 𝒟 Act) (L : LimitedSelfMod S) (aₘ : Act)
    (h : S.twin aₘ ≠ L.ac aₘ) :
    P.pairMass (L.ob aₘ) (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) = 0 ∧
    cellEU P (L.ob aₘ) (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) = 0 :=
  slides028_restrictedCoord_literal_null P (L.ob aₘ) h

/-- **The fix, verified**: under Limited Self-Modification, a self-modifying action available at `o`
never targets `o` itself, so the fairness cell of Theorem 3 is never the degenerate one.
Source: bli-slides-045 ("can't modify itself"); `main.tex` 207 (`aₘ ∉ 𝒜_{ob(aₘ)}`)
Kind: L
Fidelity: exact
Hyps: (a) `LimitedSelfMod` -/
theorem lsm_ob_ne (S : PaperStructure 𝒟 Act) (L : LimitedSelfMod S) {o : ↥𝒟} {aₘ : Act}
    (hm : aₘ ∈ S.selfMod) (ha : aₘ ∈ S.Aof o) : o ≠ L.ob aₘ := by
  intro h
  rw [h] at ha
  exact L.not_self aₘ hm ha

/-! ## T14: value relevance -/

/-- **Value relevance** (bli-paper-2-022's repair): no single action is an updateful choice at
every table of positive mass — exactly the condition of `udt-bli-core`'s `good_strict_iff`.
Source: bli-paper-2-022 (Phase 3.1 "Value-Relevance", garbled; repaired as positive value of
information); mandate T14
Kind: D
Fidelity: variant: the repaired, well-posed form -/
def ValueRelevant : Prop := ¬ ∃ a, ∀ T, 0 < P.stateMass T → P.IsUpdatefulChoice T a

/-- **Value relevance is "the updateful policy strictly beats every constant policy"** (positive
value of information), under `udt-bli-core`'s hypotheses for Good's theorem.
Source: bli-paper-2-022; `udt-bli-core` `good_strict_iff`
Kind: L
Fidelity: exact
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`, an updateful policy -/
theorem valueRelevant_iff_good_strict (hpol : P.NDPOLICY) (hR : P.ReflectivePolicy)
    (hL : P.LocalUtility) (πu : Policy 𝒟 Act) (hu : P.IsUpdatefulPolicy πu) :
    ValueRelevant P ↔ ∀ a, P.exAnteValue (fun _ => a) < P.exAnteValue πu :=
  (P.good_strict_iff hpol hR hL πu hu).symm

end Cleanroom.Udt.UdtPaperTiling
