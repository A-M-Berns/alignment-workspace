import Cleanroom.Udt.UdtCommTrust.Concrete
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt
import Cleanroom.Udt.UdtCtExamples.Infra
import Cleanroom.Udt.UdtCtExamples.CoordButtons

/-!
# `Cleanroom.Udt.UdtCtExamples.Modification`: behavioural versus forcing modification (T7(b))

Work package `udt-ct-examples`, target T7(b) (bli-paper-2-018). Source: the Claude write-up in
[[udt-tiling-working-notes-2025-06-30]] lines 336–348 and 390 (modification as "the effective
policy differs from the chosen one", per instance, against the LaTeX's *forcing* definition
`dom(q_ǒ) ≠ ∅` — `udt-comm-trust`'s `IsModified`, `modProb`).

* `ModBeh ω := Π†(ω) ≠ Π*(ω)` (behavioural), `evModBeh`, `modProbBeh` (junk `0`);
  `GlobalLink S := ∀ ω, ¬ IsModified ω → Π†(ω) = Π*(ω)` — *incomparable* with the `hlink` of
  `aE_follows_R_of_udtRuleAt` (audit r1 N4): its conclusion is global (full policies, not the
  realized input) but its antecedent `¬ IsModified ω` (no instance forced) is stronger than
  `hlink`'s `P ω (Ö ω) = none` (the realized instance unforced), so a world forced at another
  instance but not at its own is covered by `hlink` only.
  On the package's own three-instance witnesses the behavioural notion is degenerate (audit r1
  N3, probe `BehModOnWitnesses`): on `TB` (and `CB`) `Π†(ȯ, pre) = ȯ` while `Π*(ȯ, pre) = s`,
  so the full policies differ at the unrealized input `(1 − s, pre)` at *every* world,
  `ModBeh` holds everywhere, `modProbBeh = 1` on every non-empty event and `GlobalLink` fails;
  on `CBm` the opposite, `Π† = Π*` at every world, so the pill there is harmless forcing (the
  chosen policy already presses `$10` on an active channel), and so is the pill on `TB`, whose
  chosen policy reads the channel too. **Not on `CB`** (audit r2, fidelity B2 / adversarial B1;
  the first version of this docstring said otherwise): `CB`'s chosen policy presses `k` at a
  room whatever it observes, so at the `(pill, $5)` worlds the pill overrides a `$5` press at the
  *realized* input — `CB.pill_overrides_five`, and `CB.modBeh_pill_five` below — and is harmless
  only at the `(pill, $10)` worlds (`CB.pill_harmless_ten`); `m(pill) = 1` on `CB` counts forcing
  that is behavioural with probability `P(k = $5)`. `CB` is thus the package's witness of forcing
  *with* behavioural modification at a realized input, the counterpart of `HF`. Findings F-9.
* (i) `GlobalLink → evModBeh ⊆ evMod`: behavioural modification is forcing modification.
* (ii) The converse fails: `HF` (four worlds) has *harmless forcing* — the side channel forces
  the action the chosen policy takes anyway — with mass `4/5`; and in general
  `modProb e − modProbBeh e = P(IsModified ∧ ¬ ModBeh ∣ e)` on a non-empty `e` under
  `GlobalLink`.
* (iii) On `HF`, the action whose chosen-policy event is forced with probability `7/8` is
  minimally modifying behaviourally (`MinModBeh`, every action has behavioural modification
  probability `0`) and not under forcing (`MinMod` fails: `7/8 > 1/8`): the subject of the
  Self-Trust theorem changes with the definition.
* (iv) bli-paper-2-018(b), the write-up's per-instance/global inconsistency, is the same
  witness read through lines 336–348 and 390: findings F-9.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OI] [Fintype OE] [DecidableEq OI] [DecidableEq OE] [DecidableEq AI] [DecidableEq AE]
  [Fintype AE]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- **Behavioural modification**: the effective policy differs from the chosen one.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 336–348 (bli-paper-2-018)
Kind: D
Fidelity: exact (as full policies)
Hyps: n/a -/
def ModBeh (ω : Ω) : Prop := S.polD ω ≠ S.polS ω

/-- The behavioural modification event.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def evModBeh : Finset Ω := event fun ω => S.polD ω ≠ S.polS ω

/-- **The behavioural modification probability** `P(Π† ≠ Π* ∣ e)`, junk `0`.
Source: [[udt-tiling-working-notes-2025-06-30]] line 348 (bli-paper-2-018)
Kind: D
Fidelity: exact (junk `0`, as `modProb`)
Hyps: n/a -/
noncomputable def modProbBeh (e : Finset Ω) : ℝ := condProbJunk S.μ.w (evModBeh S) e 0

/-- **`GlobalLink`**: wholly unforced worlds have `Π† = Π*` as full policies. Incomparable with
`hlink` (global conclusion, but only at worlds unforced at *every* instance; `hlink` speaks at
the realized input of every world unforced at its *own* instance) — audit r1 N4; the module
docstring has the comparison.
Source: mandate T7(b)
Kind: D
Fidelity: n/a (this package's name for the global form)
Hyps: n/a -/
def GlobalLink : Prop := ∀ ω, ¬ S.IsModified ω → S.polD ω = S.polS ω

/-- **(i) Under `GlobalLink`, behavioural modification is forcing modification.**
Source: mandate T7(b)(i)
Kind: L
Fidelity: exact
Hyps: none -/
theorem evModBeh_subset_evMod (h : GlobalLink S) : evModBeh S ⊆ S.evMod := by
  intro ω hω
  rw [evModBeh, mem_event] at hω
  rw [ConcreteDS.evMod, mem_event]
  by_contra hne
  exact hω (h ω hne)

/-- **(ii) The gap between the two probabilities is the harmless-forcing probability**: under
`GlobalLink`, on a non-empty `e`, `modProb e − modProbBeh e = P(IsModified ∧ ¬ ModBeh ∣ e)`.
Source: mandate T7(b)(ii)
Kind: P
Fidelity: exact
Hyps: (a) `GlobalLink`; §3 (c) -/
theorem modProb_sub_modProbBeh (h : GlobalLink S) {e : Finset Ω} (he : e.Nonempty) :
    S.modProb e - modProbBeh S e = condProbJunk S.μ.w (S.evMod \ evModBeh S) e 0 := by
  unfold ConcreteDS.modProb modProbBeh
  rw [condProbJunk_of_nonempty S.pos he, condProbJunk_of_nonempty S.pos he,
    condProbJunk_of_nonempty S.pos he, ← sub_div]
  congr 1
  have hsub : evModBeh S ∩ e ⊆ S.evMod ∩ e :=
    Finset.inter_subset_inter_right (evModBeh_subset_evMod S h)
  have hsd : (S.evMod ∩ e) \ (evModBeh S ∩ e) = (S.evMod \ evModBeh S) ∩ e := by
    ext ω
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [← hsd, mass, mass, mass, ← Finset.sum_sdiff hsub]
  ring

/-- **Behavioural minimal modification**: `modProbBeh (Π*(ȯ,ö) = a) ≤ modProbBeh (Π*(ȯ,ö) = a')`
for every attained `a'`.
Source: [[udt-tiling-working-notes-2025-06-30]] line 348, in the shape of `MinMod`
Kind: D
Fidelity: exact (as `MinMod`, with the behavioural probability)
Hyps: n/a -/
noncomputable def MinModBeh (o : OI) (e : OE) (a : AI × AE) : Prop :=
  ∀ a', (S.evS o e a').Nonempty → modProbBeh S (S.evS o e a) ≤ modProbBeh S (S.evS o e a')

end General

/-! ### `HF`: harmless forcing -/

namespace HF

/-- Worlds `(c, k)`: `c` the channel (`1` forces action `1`), `k` the chosen policy (`0`: press
the channel value; `1`: press `1` always). Weights: `7 : 1` towards `c = 1` when `k = 1`, uniform
when `k = 0`.
Source: none: infrastructure (mandate T7(b)(ii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- The weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.2 = 1 then (if ω.1 = 1 then 7 else 1) else 1
  pos ω := by revert ω; decide
  N := 10
  sum_eq := by decide +kernel

/-- The external action: `1` when forced, else the chosen policy's press `k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def act (ω : Ω) : Fin 2 := if ω.1 = 1 then 1 else ω.2

/-- The chosen policy of `k`: `k = 0` presses the channel value, `k = 1` presses `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (k : Fin 2) : Policy (Fin 2 × Fin 1) (Fin 1 × Fin 2) :=
  if k = 0 then (fun o => (0, o.1)) else fun _ => (0, 1)

/-- **`HF` as an abstract decision structure**: `Ȯ = Ǒ = D_I = c`, `D_B = k`, `Ä = act`,
`U = Ä`.
Source: mandate T7(b)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 1) (Fin 2)
    (Fin 1) (Fin 2) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1
  oE _ := 0
  aI _ := 0
  aE := act
  dI ω := ω.1
  dE _ := 0
  dB ω := ω.2
  oH _ := 0
  oC ω := ω.1
  polS ω := polOf' ω.2
  U := natDiv (fun ω => if act ω = 1 then 1 else 0) 1
  U_mem := natDiv_mem _ (by norm_num) (fun ω => by split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`HF` as a concrete decision structure**: channel value `1` forces action `1`.
Source: mandate T7(b)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 1) (Fin 2)
    (Fin 1) (Fin 2) where
  toAbstractDS := absDS
  s _ _ := none
  p _ c := if c = 1 then some 1 else none

/-- **`Π†` on `HF`**: `o ↦ (0, 1)` if the observed channel is `1`, else `(0, k)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun o => (0, if o.1 = 1 then 1 else ω.2) :=
  polD_eq_of S.toAbstractDS (fun ω o => (0, if o.1 = 1 then 1 else ω.2)) (fun _ => rfl)
    (fun ω ω' h => by show (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), if o.1 = 1 then (1 : Fin 2) else ω.2)) = _; rw [show ω.2 = ω'.2 from h])
    (by decide +kernel) ω

/-- **No behavioural modification on `HF`**: `Π† = Π*` at every world — the forcing is harmless.
Source: mandate T7(b)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_modBeh (ω : Ω) : ¬ ModBeh S ω := by
  unfold ModBeh
  rw [polD_eq]
  show ¬ ((fun o : Fin 2 × Fin 1 => ((0 : Fin 1), if o.1 = 1 then (1 : Fin 2) else ω.2)) ≠ polOf' ω.2)
  revert ω
  decide

/-- Supporting lemma `evModBeh_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evModBeh_eq : evModBeh S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ω hω
  rw [evModBeh, mem_event] at hω
  exact not_modBeh ω hω

/-- Supporting lemma `evMod_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : S.evMod = event fun ω : Ω => ω.1 = 1 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 1, ((if ω.1 = 1 then some (1 : Fin 2) else none)).isSome) ↔ ω.1 = 1
  revert ω
  decide

/-- **`GlobalLink` holds on `HF`** (trivially: `Π† = Π*` everywhere).
Source: mandate T7(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem globalLink : GlobalLink S := fun ω _ => by
  by_contra h
  exact not_modBeh ω h

/-- **Forcing modification has mass `4/5` on `HF`, behavioural modification mass `0`**: the
converse of `evModBeh_subset_evMod` fails.
Source: mandate T7(b)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem harmless_forcing : mass S.μ.w S.evMod = 4 / 5 ∧ mass S.μ.w (evModBeh S) = 0 := by
  constructor
  · rw [evMod_eq]
    show mass weights.w _ = _
    rw [weights.mass_eq_cnt]
    have : weights.cnt (event fun ω : Ω => ω.1 = 1) = 8 := by decide +kernel
    rw [this]
    show ((8 : ℕ) : ℝ) / ((10 : ℕ) : ℝ) = 4 / 5
    norm_num
  · rw [evModBeh_eq]
    simp [mass]

/-- Supporting lemma: attainment at the unforced input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_nonempty (x : Fin 2) : (S.evS 0 0 (0, x)).Nonempty :=
  ⟨(0, x), by rw [AbstractDS.mem_evS]; show polOf' x (0, 0) = (0, x); revert x; decide⟩

/-- **(iii) On `HF`, at the unforced input, the action `1` is minimally modifying behaviourally
and not under forcing**: both behavioural probabilities are `0`; the forcing probabilities are
`7/8` for action `1` (the `k = 1` policies are forced with weight `7 : 1`) against `1/2` for
action `0`. The subject of the Self-Trust theorem changes with the definition.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 336–348 (bli-paper-2-018(d)); mandate T7(b)(iii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem minModBeh_not_minMod : MinModBeh S 0 0 (0, 1) ∧ ¬ S.MinMod 0 0 (0, 1) := by
  constructor
  · intro a' ha'
    unfold modProbBeh
    rw [evModBeh_eq, condProbJunk_eq_zero_of_disjoint S.pos (evS_nonempty 1) (Finset.empty_inter _),
      condProbJunk_eq_zero_of_disjoint S.pos ha' (Finset.empty_inter _)]
  · intro h
    have := h (0, 0) (evS_nonempty 0)
    unfold ConcreteDS.modS ConcreteDS.modProb at this
    rw [evMod_eq] at this
    have hlt : condProbJunk S.μ.w (event fun ω : Ω => ω.1 = 1) (S.evS 0 0 (0, 0)) 0 <
        condProbJunk S.μ.w (event fun ω : Ω => ω.1 = 1) (S.evS 0 0 (0, 1)) 0 := by
      refine condProbJunk_lt_of_cnt weights (evS_nonempty 0) (evS_nonempty 1) ?_
      show weights.cnt (_ ∩ event fun ω : Ω => polOf' ω.2 (0, 0) = (0, 0)) *
          weights.cnt (event fun ω : Ω => polOf' ω.2 (0, 0) = (0, 1)) <
        weights.cnt (_ ∩ event fun ω : Ω => polOf' ω.2 (0, 0) = (0, 1)) *
          weights.cnt (event fun ω : Ω => polOf' ω.2 (0, 0) = (0, 0))
      decide +kernel
    exact absurd this (not_le.2 hlt)

/-- **The gap on `HF`**: at the action-`1` event, `modProb − modProbBeh = 7/8`, the harmless
forcing probability (`modProb_sub_modProbBeh` instantiated).
Source: mandate T7(b)(ii)
Kind: C
Fidelity: n/a
Hyps: none -/
theorem gap_witness :
    S.modProb (S.evS 0 0 (0, 1)) - modProbBeh S (S.evS 0 0 (0, 1)) =
      condProbJunk S.μ.w (S.evMod \ evModBeh S) (S.evS 0 0 (0, 1)) 0 :=
  modProb_sub_modProbBeh S globalLink (evS_nonempty 1)

end HF

namespace CB

/-- **On `CB` the pill is a behavioural modification at every `$5`-policy pill world**
(`Π†(ω) ≠ Π*(ω)` as full policies, witnessed at the *realized* room input by
`pill_overrides_five`), for every prior: forcing *with* behavioural modification, the
counterpart of `HF`'s harmless forcing. Lifted from the audit-r2 probe
`CbPillOverridesPolicy.modBeh` (repair round 2).
Source: [[udt-tiling-working-notes-2025-06-30]] lines 336–348 (bli-paper-2-018); audit r2 (adversarial B1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modBeh_pill_five (W : IntWeights Ω) (e : Fin 3) (a : Fin 2) (he : e ≠ 0) :
    ModBeh (S W) ((1, 0), (e, a)) := fun h =>
  pill_overrides_five W e a he (congrFun h _)

end CB

end Cleanroom.Udt.UdtCtExamples
