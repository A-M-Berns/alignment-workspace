import Cleanroom.Udt.UdtCommTrust.Concrete
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt
import Cleanroom.Udt.UdtCtExamples.Infra

/-!
# `Cleanroom.Udt.UdtCtExamples.NonInterference`: two incompatible non-interference
formalizations (T4)

Work package `udt-ct-examples`, target T4 (udt-rep-027). Source: [[non-interference-formalized]]
lines 96–124: the note attributes to the paper "the agent has self-trust if it never strictly
prefers modification opportunities over non-modification. Formally: `E[U ∣ Π† = Π*] ≥
E[U ∣ Π† ≠ Π*]`" (lines 100–105) and states its own multi-agent notion "Non-interference:
`a'_o = a_o` for all `o`" (line 113: each instance's *actual* action is its *chosen* action), then
claims "Under rationality, no preference implies no actual" (line 120).

**Neither definition is in C&T.** The paper's Self-Trust theorem is `selfTrust_repaired`
(`udt-comm-trust`): at every input, some minimally modifying action is a UDT argmax. `NIPref`
below is the note's "paper's form" made exact (junk `−1` on the empty event); `NIAct` is the
multi-agent form read as "effective = chosen at every world" (ATTRIBUTION-UNVETTED; the
at-realized-input variant `NIActRealized` is also stated, and is `udt-comm-trust`'s `hlink`
without the unforced guard). The two are about different objects: `NIPref` compares utilities
across the modification/no-modification partition, `NIAct` says the partition's second cell is
empty. (i) `NIAct → NIPref` is a junk artifact (the `≠` event is empty and scores `−1`); (ii) a
four-world witness has `NIPref` (a tie) with modification of mass `1/2`, so `NIPref` does not
give `NIAct`; (iii) the note's "under rationality, no preference implies no actual" has no
one-line neighbour in the package (findings F-7): `Π† ≠ Π*` is about forcing, and the strict
argmax ceiling `minMod_of_isStrictArgmax` gives minimal, not zero, modification probability.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OI] [Fintype OE] [DecidableEq AI] [DecidableEq AE]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- The event `{Π† = Π*}`.
Source: [[non-interference-formalized]] line 104
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def evAgree : Finset Ω := event fun ω => S.polD ω = S.polS ω

/-- The event `{Π† ≠ Π*}`.
Source: [[non-interference-formalized]] line 104
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def evDisagree : Finset Ω := event fun ω => S.polD ω ≠ S.polS ω

/-- **`NIPref`**: the note's "paper's form" of self-trust,
`E[U ∣ Π† = Π*] ≥ E[U ∣ Π† ≠ Π*]` (junk `−1`). **Not in C&T**: the paper's theorem is
`selfTrust_repaired`.
Source: [[non-interference-formalized]] lines 100–105 (udt-rep-027)
Kind: D
Fidelity: exact for the note's display; the attribution to the paper is the note's (findings F-7)
Hyps: n/a -/
noncomputable def NIPref : Prop :=
  condExpJunk S.μ.w S.U (evAgree S) (-1) ≥ condExpJunk S.μ.w S.U (evDisagree S) (-1)

/-- **`NIAct`**: the multi-agent non-interference "`a'_o = a_o` for all `o`", read as: the
effective policy is the chosen policy at every world (ATTRIBUTION-UNVETTED).
Source: [[non-interference-formalized]] line 113 (udt-rep-027)
Kind: D
Fidelity: variant: "for all `o`" read as "at every world, as full policies"
Hyps: n/a -/
def NIAct : Prop := ∀ ω, S.polD ω = S.polS ω

/-- **`NIActRealized`**: the at-realized-input variant, `Π†(ω)(O(ω)) = Π*(ω)(O(ω))` at every
world — `hlink` without its unforced guard.
Source: [[non-interference-formalized]] line 113, alternative reading
Kind: D
Fidelity: variant: at the realized input only
Hyps: n/a -/
def NIActRealized : Prop := ∀ ω, S.polD ω (S.O ω) = S.polS ω (S.O ω)

/-- Supporting lemma `NIAct.toRealized`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem NIAct.toRealized (h : NIAct S) : NIActRealized S := fun ω => by rw [h ω]

/-- **(i) `NIAct → NIPref`, a junk artifact**: under `NIAct` the disagreement event is empty and
scores the junk `−1`, below the agreement event's (non-negative) score. Said plainly: the
implication holds for every structure with a `[0,1]`-valued utility, whatever the utility does.
Source: [[non-interference-formalized]] line 120 (the direction the note does not claim); mandate T4(i)
Kind: L
Fidelity: exact (the implication is the junk convention at work)
Hyps: none -/
theorem niPref_of_niAct (h : NIAct S) : NIPref S := by
  have h1 : evDisagree S = ∅ := by
    ext ω
    simp [evDisagree, h ω]
  have h2 : evAgree S = univ := by
    ext ω
    simp [evAgree, h ω]
  unfold NIPref
  rw [h1, h2, condExpJunk_of_empty]
  exact (junk_lt_of_nonempty S.pos S.U_nonneg (Finset.univ_nonempty_iff.2 S.nonempty)).le

end General

/-! ### `NI4`: `NIPref` with modification of positive mass and `¬ NIAct` -/

namespace NI4

/-- Worlds `(k, c)`: `k` the dynamics (`0` unforced, chosen policy reads the channel; `1` forced
to press `1`, chosen policy presses `0`), `c` a coin.
Source: none: infrastructure (mandate T4(ii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights on four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The utility numerator: the action matches the coin.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.1 = ω.2 then 1 else 0

/-- The chosen policy: at `k = 0` it reads the channel value and presses it; at `k = 1` it
presses `0` whatever it observes (and is forced to `1`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (k : Fin 2) : Policy (Fin 2 × Fin 1) (Fin 1 × Fin 2) :=
  if k = 0 then (fun o => (0, o.1)) else fun _ => (0, 0)

/-- **`NI4` as an abstract decision structure**: one instance; `Ȯ = Ǒ = D_I = k`; `Ä = k`; the
coin is `D_E`; `U = 𝟙[Ä = coin]`.
Source: mandate T4(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 1)
    (Fin 1) (Fin 2) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1
  oE _ := 0
  aI _ := 0
  aE ω := ω.1
  dI ω := ω.1
  dE ω := ω.2
  dB _ := 0
  oH _ := 0
  oC ω := ω.1
  polS ω := polOf' ω.1
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`NI4` as a concrete decision structure**: no messages; channel value `1` forces action `1`.
Source: mandate T4(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 1)
    (Fin 1) (Fin 2) where
  toAbstractDS := absDS
  s _ _ := none
  p _ c := if c = 1 then some 1 else none

/-- **`Π†` on `NI4`**: the same function at every world, `o ↦ (0, o.1)` (press what the channel
says).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun o => (0, o.1) :=
  polD_eq_of S.toAbstractDS (fun _ o => (0, o.1)) (fun _ => rfl) (fun _ _ _ => rfl)
    (by decide +kernel) ω

/-- Supporting lemma: the agreement and disagreement events on the coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evAgree_eq : (evAgree S.toAbstractDS = event fun ω : Ω => ω.1 = 0) ∧
    (evDisagree S.toAbstractDS = event fun ω : Ω => ω.1 = 1) := by
  constructor
  · unfold evAgree
    refine event_congr fun ω => ?_
    rw [polD_eq]
    show (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) = polOf' ω.1 ↔ ω.1 = 0
    revert ω
    decide
  · unfold evDisagree
    refine event_congr fun ω => ?_
    rw [polD_eq]
    show (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) ≠ polOf' ω.1 ↔ ω.1 = 1
    revert ω
    decide

/-- **`NIPref` holds on `NI4`**, as a tie: both cells score `1/2`.
Source: mandate T4(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem niPref : NIPref S.toAbstractDS := by
  unfold NIPref
  rw [evAgree_eq.1, evAgree_eq.2]
  exact (condExpJunk_natDiv_eq weights u (by norm_num) (by decide) (by decide) (by decide +kernel)
    (-1)).ge

/-- **`NIAct` fails on `NI4`**: at the forced worlds the chosen policy presses `0` and the
effective one `1`.
Source: mandate T4(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_niAct : ¬ NIAct S.toAbstractDS := fun h => by
  have := h (1, 0)
  rw [polD_eq] at this
  have h2 : (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) ≠ polOf' 1 := by decide
  exact h2 this

/-- **Modification has mass `1/2` on `NI4`**: the forced worlds are half the support.
Source: mandate T4(ii) ("modification of positive mass")
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modification_mass : mass S.μ.w S.evMod = 1 / 2 := by
  have h : S.evMod = event fun ω : Ω => ω.1 = 1 := by
    ext ω
    simp only [ConcreteDS.evMod, mem_event]
    show (∃ e : Fin 1, ((if ω.1 = 1 then some (1 : Fin 2) else none)).isSome) ↔ ω.1 = 1
    revert ω
    decide
  rw [h]
  show mass weights.w _ = _
  rw [weights.mass_eq_cnt]
  have : weights.cnt (event fun ω : Ω => ω.1 = 1) = 2 := by decide +kernel
  rw [this]
  show ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 1 / 2
  norm_num

/-- **`NIPref ∧ ¬ NIAct` on `NI4`** (T4(ii)): the note's two definitions come apart on a
four-world structure where modification has mass `1/2` and the utilities tie.
Source: [[non-interference-formalized]] lines 100–120; mandate T4(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem niPref_not_niAct : NIPref S.toAbstractDS ∧ ¬ NIAct S.toAbstractDS ∧
    mass S.μ.w S.evMod = 1 / 2 :=
  ⟨niPref, not_niAct, modification_mass⟩

end NI4

end Cleanroom.Udt.UdtCtExamples
