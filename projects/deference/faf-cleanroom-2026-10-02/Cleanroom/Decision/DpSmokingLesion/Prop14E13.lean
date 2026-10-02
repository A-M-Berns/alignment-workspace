import Cleanroom.Decision.DpSmokingLesion.Prop13

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T4(c)(d): the compulsion E13 — action-veridicality failure, honest at all five grades

[[dp-smoking-lesion-mandate]] T4(c)(d) and the general lemma of T11.

* **T11's lemma** (`perRunClausesAt_iff_strictClausesAt_of_occ_univ`, `perRunSSCAt_iff_strictOCAt_of_occ_univ`):
  when every run consults `d` (`occ(d) = univ`) the per-run SSC clauses at `d` are the strict
  clauses at `O_d = ⊤` — both condition on `ν`.
* **E13 at the FDT numbers, `c = (9/10, 1/10)`** (`e13₀`): the four (S2) masses as closed forms
  in the label `q` (`e13_nu_values`: `ν(m=1) = (1+q)/2`, `ν(k ∧ m=1) = (223 + 27q)/500`,
  `ν(m=0) = (1−q)/2`, `ν(k ∧ m=0) = 27(1−q)/500`), the gap `49(1−q)/250` (`e13_gap`), so
  (S2) holds at the strictly calibrated state for every label `q < 1` (`e13_S2_calibrated`);
  every run meets `d` (`e13_count`, `e13_occ`), so `Covers` holds (`e13_covers`) and the
  per-run and per-occurrence states are the strict state (`e13_perRun_iff_strict`,
  `e13_perOcc_iff_perRun`); recording fails at clause 3 for `q < 1` (`e13_not_recordsFor`: the
  run "lesion, drew refrain, forced" has world `m = 1`); limit and masked (interior self-model)
  likewise. **(S2) is honest at all five grades** (`prop14_e13_honest_all_grades`).
* The verdicts at `C(d) = ½` (`e13_verdicts`): `V(smoke) = −1 889 000/3 < −108 000 = V(refrain)`
  (EDT refrains, both acts in `A_d^+`), R1-state `(−499 000, −499 500)` smokes, R2-SIA
  `(−499 000, −499 500)/1` smokes, and R2-real is undefined — no `d`-node is a.s.
  node-action-veridical (`e13_realFiber_empty`).
* **(d) Recording the draw dissolves E13** (`e13Rec`): on the enriched algebra `(ℓ, m, k, m_d)`
  with action events `{m_d = ·}`, the tree records for every procedure
  (`e13Rec_recordsFor`) and the act values are `V(m_d = 1) = −499 000 > −499 500 = V(m_d = 0)`
  (`e13Rec_values`): the correlation was written by the override, not the draw.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## T11's lemma: when every run consults `d`, per-run SSC is strict OC at `⊤` -/

section occUniv

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (s : ι → State Ω K)

/-- **When `occ(d)` is every run, the per-run clauses at `d` are the strict clauses at
`O_d = ⊤`**: both sides are `ν` and `𝔼_μ[r · 1_X]`.
Source: dp-sl-2-031 ("`occ(d)` is every run, so the SSC state equals `ν`"); mandate T11
Kind: L -/
theorem perRunClausesAt_iff_strictClausesAt_of_occ_univ (hocc : occ d B = Finset.univ) :
    PerRunClausesAt s C B d ↔ StrictClausesAt s (fun _ => Finset.univ) C B d := by
  unfold PerRunClausesAt StrictClausesAt PerRunClause1At PerRunClause2At StrictClause1At
    StrictClause2At
  simp only [hocc, Finset.inter_univ, mass_univ, nu_univ]
  unfold nu paySum
  exact Iff.rfl

/-- **Per-run SSC at `d` is strict OC at `⊤` when every run consults `d`** (the guards
coincide: `μ(occ) = 1 = ν(⊤)`).
Source: dp-sl-2-031; mandate T11
Kind: C
Fidelity: exact
Hyps: (a) `occ d B = univ` -/
theorem perRunSSCAt_iff_strictOCAt_of_occ_univ (hocc : occ d B = Finset.univ) :
    PerRunSSCAt s C B d ↔ StrictOCAt s (fun _ => Finset.univ) C B d := by
  unfold PerRunSSCAt StrictOCAt
  rw [hocc, mass_univ, nu_univ, perRunClausesAt_iff_strictClausesAt_of_occ_univ C B d s hocc]

end occUniv

/-! ## E13 at the numbers -/

section e13

/-- The compulsion block after a drawn refusal at lesion index `i`: the override coin, then the
cancer block with the realized act.
Source: `sl_zoo.py` line 730
Kind: D -/
def e13Forced (i : Fin 2) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 (Compulsion.e13Rates.coinF (decide (i = 0))) fun j =>
    kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) (decide (j = 0))

/-- **E13 at the mandate's numbers**: the FDT lesion, `c = (9/10, 1/10)`, `α = 1000`, `β = 10⁶`.
Source: mandate §3.7; `sl_zoo.py` lines 716–735
Kind: D -/
def e13₀ : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 Lesion.fdt.coinL fun i =>
    .decision () fun md =>
      cond md (kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) true) (e13Forced i)

/-- `e13₀` is the catalogue tree `e13` at the mandate's parameters. Source: none: infrastructure. Kind: L -/
theorem e13₀_eq : e13₀ = e13 Lesion.fdt Compulsion.e13Rates 1000 1000000 := rfl

/-- A sum over the leaves of `e13₀`: per lesion branch, the two "drew smoke" leaves and the
four "drew refrain" leaves.
Source: none: infrastructure. Kind: L -/
theorem e13_sum (f : e13₀.Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ j : Fin 2, f ⟨i, true, j, ()⟩) +
      ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩) := by
  unfold e13₀ at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Fintype.sum_bool]
  have h1 : (∑ ℓ, f ⟨i, true, ℓ⟩) = ∑ j : Fin 2, f ⟨i, true, j, ()⟩ := by
    show (∑ ℓ : (kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) true).Leaves, f ⟨i, true, ℓ⟩) = _
    unfold kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  have h2 : (∑ ℓ, f ⟨i, false, ℓ⟩) = ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩ := by
    show (∑ ℓ : (e13Forced i).Leaves, f ⟨i, false, ℓ⟩) = _
    unfold e13Forced kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun fc _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  rw [h1, h2]

/-- The "drew smoke" leaf masses of `e13₀`: `½ · C(d)(1) · γ_{ℓ,k}`.
Source: Definition 6 on E13
Kind: L -/
theorem e13_leafLaw_smoke (C : Proc Unit (fun _ => Bool) ℚ) (i j : Fin 2) :
    leafLaw C e13₀ ⟨i, true, j, ()⟩ =
      (1/2 : ℚ) * (C ()).w true *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold e13₀
  rw [leafLaw_chance, leafLaw_decision]
  show (Lesion.fdt.coinL).w i * ((C ()).w true *
    leafLaw C (kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) true) ⟨j, ()⟩) = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, FinDistr.coin, tickleGamma,
    Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The "drew refrain" leaf masses of `e13₀`: `½ · C(d)(0) · c_{ℓ,fc} · γ_{ℓ,k}` (`fc = 0` =
forced to smoke).
Source: Definition 6 on E13
Kind: L -/
theorem e13_leafLaw_refrain (C : Proc Unit (fun _ => Bool) ℚ) (i fc j : Fin 2) :
    leafLaw C e13₀ ⟨i, false, fc, j, ()⟩ =
      (1/2 : ℚ) * (C ()).w false *
        (if i = 0 then (if fc = 0 then 9/10 else 1/10) else (if fc = 0 then 1/10 else 9/10)) *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold e13₀
  rw [leafLaw_chance, leafLaw_decision]
  show (Lesion.fdt.coinL).w i * ((C ()).w false * leafLaw C (e13Forced i) ⟨fc, j, ()⟩) = _
  unfold e13Forced kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, Compulsion.coinF,
    FinDistr.coin, tickleGamma, Lesion.fdt, Compulsion.e13Rates]
  fin_cases i <;> fin_cases fc <;> fin_cases j <;> simp <;> ring

/-- The worlds at the leaves of `e13₀`: the realized act is `1` after a drawn smoke, and after a
drawn refrain it is `1` iff the override fired.
Source: `sl_zoo.py` line 733 ("the realized `m` only")
Kind: L -/
theorem e13_world :
    (∀ (i j : Fin 2), world e13₀ ⟨i, true, j, ()⟩ = (decide (i = 0), true, decide (j = 0))) ∧
    (∀ (i fc j : Fin 2),
      world e13₀ ⟨i, false, fc, j, ()⟩ = (decide (i = 0), decide (fc = 0), decide (j = 0))) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The payoffs at the leaves of `e13₀`. Source: none: infrastructure. Kind: L -/
theorem e13_payoff :
    (∀ (i j : Fin 2), payoff e13₀ ⟨i, true, j, ()⟩ =
      ticklePay 1000 1000000 (decide (i = 0), true, decide (j = 0))) ∧
    (∀ (i fc j : Fin 2), payoff e13₀ ⟨i, false, fc, j, ()⟩ =
      ticklePay 1000 1000000 (decide (i = 0), decide (fc = 0), decide (j = 0))) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- `ν` on `e13₀` as an explicit twelve-term sum. Source: none: infrastructure. Kind: L -/
theorem e13_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C e13₀ X =
      ∑ i : Fin 2, ((∑ j : Fin 2, if (decide (i = 0), true, decide (j = 0)) ∈ X then
          leafLaw C e13₀ ⟨i, true, j, ()⟩ else 0) +
        ∑ fc : Fin 2, ∑ j : Fin 2,
          if (decide (i = 0), decide (fc = 0), decide (j = 0)) ∈ X then
            leafLaw C e13₀ ⟨i, false, fc, j, ()⟩ else 0) := by
  rw [nu_eq_sum, e13_sum]
  rfl

/-- `paySum` on `e13₀` as an explicit twelve-term sum. Source: none: infrastructure. Kind: L -/
theorem e13_paySum (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    paySum C e13₀ X =
      ∑ i : Fin 2, ((∑ j : Fin 2, if (decide (i = 0), true, decide (j = 0)) ∈ X then
          leafLaw C e13₀ ⟨i, true, j, ()⟩ *
            ticklePay 1000 1000000 (decide (i = 0), true, decide (j = 0)) else 0) +
        ∑ fc : Fin 2, ∑ j : Fin 2,
          if (decide (i = 0), decide (fc = 0), decide (j = 0)) ∈ X then
            leafLaw C e13₀ ⟨i, false, fc, j, ()⟩ *
              ticklePay 1000 1000000 (decide (i = 0), decide (fc = 0), decide (j = 0)) else 0) := by
  rw [paySum_eq_sum_ite, e13_sum]
  rfl

variable (C : Proc Unit (fun _ => Bool) ℚ)

/-- **The four (S2) masses on E13 as closed forms in the label `q = C(d)(smoke)`**:
`ν(m=1) = (1+q)/2`, `ν(k ∧ m=1) = (223 + 27q)/500`, `ν(m=0) = (1−q)/2`,
`ν(k ∧ m=0) = 27(1−q)/500`. At `q = ½`: `¾`, `473/1000`, `¼`, `27/1000`.
Source: mandate §3.7 (recomputed); `sl-defensible-claims.md` S2 (R-b: `473/750 > 27/250`)
Kind: P
Fidelity: exact -/
theorem e13_nu_values :
    nu C e13₀ (evM true) = (1 + (C ()).w true) / 2 ∧
    nu C e13₀ (evK ∩ evM true) = (223 + 27 * (C ()).w true) / 500 ∧
    nu C e13₀ (evM false) = (1 - (C ()).w true) / 2 ∧
    nu C e13₀ (evK ∩ evM false) = 27 * (1 - (C ()).w true) / 500 := by
  have hw := w_false_eq_one_sub C
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [e13_nu]
    simp only [Fin.sum_univ_two, e13_leafLaw_smoke, e13_leafLaw_refrain, Finset.mem_inter, mem_evM,
      mem_evK]
    simp [hw]; ring

/-- **The (S2) gap on E13 is `49(1−q)/250`**: positive for every label `q < 1`.
Source: mandate T4(c)
Kind: P
Fidelity: exact -/
theorem e13_gap :
    nu C e13₀ (evK ∩ evM true) * nu C e13₀ (evM false) -
      nu C e13₀ (evK ∩ evM false) * nu C e13₀ (evM true) = 49 * (1 - (C ()).w true) / 250 := by
  obtain ⟨h1, h2, h3, h4⟩ := e13_nu_values C
  rw [h1, h2, h3, h4]; ring

/-- The two payoff masses on E13 as closed forms: `paySum(m=1) = −53 500q − 445 500`,
`paySum(m=0) = 54 000q − 54 000`.
Source: mandate T4(c) (recomputed as rationals)
Kind: L -/
theorem e13_paySum_values :
    paySum C e13₀ (evM true) = -53500 * (C ()).w true - 445500 ∧
    paySum C e13₀ (evM false) = 54000 * (C ()).w true - 54000 := by
  have hw := w_false_eq_one_sub C
  constructor <;>
  · rw [e13_paySum]
    simp only [Fin.sum_univ_two, e13_leafLaw_smoke, e13_leafLaw_refrain, mem_evM, ticklePay]
    simp [hw]; ring

/-- **(S2) at the strictly calibrated state of E13 for every label `q < 1`.**
Source: `sl-defensible-claims.md` S2 (R-b); mandate T4(c)
Kind: P
Fidelity: exact
Hyps: (a) `C(d)(smoke) < 1` (at `δ_smoke`, `ν(m=0) = 0` and (S2)'s second conditional is
undefined) -/
theorem e13_S2_calibrated (hq : (C ()).w true < 1) :
    S2 (calibratedState C e13₀ Finset.univ (nu_univ_pos _ _)) := by
  obtain ⟨h1, h2, h3, h4⟩ := e13_nu_values C
  have hq0 := (C ()).nonneg true
  unfold S2
  simp only [calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
  refine ⟨by rw [h1]; linarith, by rw [h3]; linarith, ?_⟩
  have := e13_gap C
  have hpos : 0 < 49 * (1 - (C ()).w true) / 250 := by
    apply div_pos _ (by norm_num); linarith
  linarith

/-- Every run of E13 meets `d` exactly once. Source: none: infrastructure. Kind: L -/
theorem e13_count (ℓ : e13₀.Leaves) : count () e13₀ ℓ = 1 := by
  unfold e13₀ e13Forced kBlock slLeaf at ℓ ⊢
  rcases ℓ with ⟨i, md, ℓ⟩
  cases md
  · rcases ℓ with ⟨fc, j, _⟩; rfl
  · rcases ℓ with ⟨j, _⟩; rfl

/-- `occ(d)` on E13 is every run. Source: dp-core-046 ("`occ(d)` is every run"). Kind: L -/
theorem e13_occ : occ () e13₀ = Finset.univ := by
  ext ℓ; simp [e13_count]

/-- E13 is almost fair. Source: none: infrastructure. Kind: L -/
theorem e13_almostFair : AlmostFair e13₀ := by
  intro d ℓ; cases d; exact (e13_count ℓ).le

/-- **Coverage holds on E13** for every procedure (every run consults `d`).
Source: `sl-synthesis.md` §1.1 ("Compulsion … covered, not recorded"); mandate T4(c)
Kind: L -/
theorem e13_covers : Covers slObs C e13₀ () := by
  intro ℓ _ _; rw [e13_count]; exact one_pos

/-- **Recording fails on E13 at clause 3** for every label `q < 1`: the run "lesion, drew
refrain, override fired, cancer" has positive mass and its world's act coordinate is `1`
although `0` was drawn.
Source: `sl-synthesis.md` §1.1 ("covered, not recorded (action-veridicality fails)"); mandate
T4(c)
Kind: N− -/
theorem e13_not_recordsFor (hq : (C ()).w true < 1) : ¬ RecordsFor slObs slActEv C e13₀ () := by
  intro h
  have hw := w_false_eq_one_sub C
  have hpos : 0 < leafLaw C e13₀ ⟨0, false, 0, 0, ()⟩ := by
    rw [e13_leafLaw_refrain, hw]; simp; linarith
  obtain ⟨-, h2⟩ := h ⟨0, false, 0, 0, ()⟩ hpos (Finset.mem_univ _)
  have hedge : edgeOf e13₀ ⟨0, none⟩ ⟨0, false, 0, 0, ()⟩ = some false := by
    unfold e13₀; simp [edgeOf_chance, edgeOf_decision_none]
  have hav := (h2 ⟨0, none⟩ rfl false hedge).2.1
  rw [e13_world.2] at hav
  simp [slActEv, evM] at hav

/-- **Per-run SSC on E13 is strict OC at `⊤`** (every run consults `d`).
Source: dp-sl-2-031; mandate T4(c), T11
Kind: C
Fidelity: exact
Hyps: none -/
theorem e13_perRun_iff_strict (s : Unit → State TickleW ℚ) :
    PerRunSSCAt s C e13₀ () ↔ StrictOCAt s slObs C e13₀ () :=
  perRunSSCAt_iff_strictOCAt_of_occ_univ C e13₀ () s e13_occ

/-- Per-occurrence SSC on E13 is per-run SSC (almost fair).
Source: mandate T4(c)
Kind: C
Fidelity: exact
Hyps: none -/
theorem e13_perOcc_iff_perRun (s : Unit → State TickleW ℚ) :
    PerOccSSCAt s C e13₀ () ↔ PerRunSSCAt s C e13₀ () :=
  perOccSSCAt_iff_perRunSSCAt_of_count_le_one_ae C e13₀ () s (fun ℓ _ => (e13_count ℓ).le)

/-- **Proposition 14, the action-veridicality home: (S2) is honest at all five grades on E13.**
At every label `q < 1` the strictly calibrated state at `⊤` satisfies (S2) and is strict-,
per-run- and per-occurrence-calibrated and limit-calibrated at `d`; at every interior
self-model `m` the state calibrated to `C[d ↦ m]` satisfies (S2) and is masked-calibrated for
`C`; coverage holds and recording fails (clause 3).
Source: `sl-defensible-claims.md` S2 (R-b: "(S2) holds at the calibrated state at **all five**
grades … E13: `P_s(k ∣ m=1) = 473/750 > 27/250` at the strict and per-run states alike");
dp-sl-012; dp-core-046; mandate T4(c)
Kind: C
Fidelity: exact (masked at an interior self-model; limit = strict at the realized point)
Hyps: (a) `C(d)(smoke) < 1` for the strict/SSC/limit clauses; (a) `m` full-support with
`m(smoke) < 1` (automatic for a full-support `m`) for the masked clause -/
theorem prop14_e13_honest_all_grades (hq : (C ()).w true < 1) :
    let s₀ : Unit → State TickleW ℚ := fun _ => calibratedState C e13₀ Finset.univ (nu_univ_pos _ _)
    (S2 (s₀ ()) ∧ StrictOCAt s₀ slObs C e13₀ () ∧ PerRunSSCAt s₀ C e13₀ () ∧
      PerOccSSCAt s₀ C e13₀ () ∧ LimitOCAt s₀ slObs C e13₀ ()) ∧
    (∀ m : FinDistr ℚ Bool, (∀ a, 0 < m.w a) →
      let s₁ : Unit → State TickleW ℚ :=
        fun _ => calibratedState (C.deviate () m) e13₀ Finset.univ (nu_univ_pos _ _)
      S2 (s₁ ()) ∧ MaskedOCAt s₁ slObs C e13₀ ()) ∧
    Covers slObs C e13₀ () ∧ ¬ RecordsFor slObs slActEv C e13₀ () := by
  intro s₀
  have hs : StrictOCAt s₀ slObs C e13₀ () := strictOCAt_calibratedState slObs C e13₀ s₀ () _ rfl
  refine ⟨⟨e13_S2_calibrated C hq, hs, (e13_perRun_iff_strict C s₀).mpr hs,
    (e13_perOcc_iff_perRun C s₀).mpr ((e13_perRun_iff_strict C s₀).mpr hs),
    limitOCAt_of_strictOCAt_of_pos s₀ slObs C e13₀ () (nu_univ_pos _ _) hs⟩,
    fun m hm => ?_, e13_covers C, e13_not_recordsFor C hq⟩
  intro s₁
  have hm1 : (C.deviate () m ()).w true < 1 := by
    rw [Proc.deviate_same]
    have := m.sum_one
    rw [Fintype.sum_bool] at this
    have := hm false
    linarith
  exact ⟨e13_S2_calibrated _ hm1, maskedOCAt_calibratedState slObs C e13₀ s₁ () m hm _ rfl⟩

/-! ### The verdicts at `C(d) = ½` -/

/-- The label `C(d) = ½`. Source: mandate T4(c). Kind: D -/
abbrev e13Half : Proc Unit (fun _ => Bool) ℚ := procBool (1/2) (by norm_num) (by norm_num)

/-- The `d`-node of lesion branch `i` of E13. Source: none: infrastructure. Kind: D -/
def e13Node (i : Fin 2) : e13₀.DecNode := ⟨i, none⟩

/-- Every decision node of E13 is one of the two `d`-nodes. Source: none: infrastructure. Kind: L -/
theorem e13_nodes_cases (q : e13₀.DecNode) : ∃ i : Fin 2, q = e13Node i := by
  unfold e13₀ e13Forced kBlock slLeaf at q
  rcases q with ⟨i, (_ | ⟨md, q⟩)⟩
  · exact ⟨i, rfl⟩
  · exfalso
    cases md
    · rcases q with ⟨fc, ⟨j, e⟩⟩; exact e.elim
    · rcases q with ⟨j, e⟩; exact e.elim

/-- The edge a leaf takes at the `d`-node of branch `i`. Source: none: infrastructure. Kind: L -/
theorem e13_edgeOf :
    (∀ (i i' j : Fin 2), edgeOf e13₀ (e13Node i) ⟨i', true, j, ()⟩ =
      if i' = i then some true else none) ∧
    (∀ (i i' fc j : Fin 2), edgeOf e13₀ (e13Node i) ⟨i', false, fc, j, ()⟩ =
      if i' = i then some false else none) := by
  constructor
  · intro i i' j
    unfold e13Node e13₀
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance, edgeOf_decision_none]
    · simp [edgeOf_chance, h]
  · intro i i' fc j
    unfold e13Node e13₀
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance, edgeOf_decision_none]
    · simp [edgeOf_chance, h]

/-- **Cancer is post-query independent of the draw on E13, for every procedure**: at each
`d`-node the `k`-mass below either action edge is `γ_ℓ` times the edge mass (the lesion is
decided above `d`; the override only relabels the realized act). So `prop14_only_if` applies
to E13 and the family-level "(S2) at a strict state forces recording to fail" is a theorem
about E13, not only a per-tree `¬ RecordsFor`.
Source: mandate T4(a) (`PostQueryIndep evK` on the failing trees); audit r1 adversarial N7,
fidelity §3.7
Kind: N+ -/
theorem e13_postQueryIndep (C : Proc Unit (fun _ => Bool) ℚ) : PostQueryIndep C e13₀ () evK := by
  intro q _ a b
  obtain ⟨i, rfl⟩ := e13_nodes_cases q
  have hin : ∀ a : Bool, edgeMassIn C e13₀ evK (e13Node i) a =
      1/2 * (C ()).w a * (if i = 0 then 99/100 else 1/100) := by
    intro a
    unfold edgeMassIn
    rw [e13_sum]
    simp only [Fin.sum_univ_two, e13_edgeOf.1, e13_edgeOf.2, e13_leafLaw_smoke, e13_leafLaw_refrain,
      e13_world.1, e13_world.2, mem_evK]
    fin_cases i <;> cases a <;> simp <;> ring
  have hm : ∀ a : Bool, edgeMass C e13₀ (e13Node i) a = 1/2 * (C ()).w a := by
    intro a
    unfold edgeMass
    rw [e13_sum]
    simp only [Fin.sum_univ_two, e13_edgeOf.1, e13_edgeOf.2, e13_leafLaw_smoke, e13_leafLaw_refrain]
    fin_cases i <;> cases a <;> simp <;> ring
  rw [hin, hin, hm, hm]; ring

/-- The fiber of `d` on E13 is every decision node. Source: none: infrastructure. Kind: L -/
theorem e13_fiber : fiber e13₀ () = Finset.univ := by
  ext q; simp [fiber]

/-- A sum over the decision nodes of E13. Source: none: infrastructure. Kind: L -/
theorem e13_sum_decNode (f : e13₀.DecNode → ℚ) : ∑ q, f q = f (e13Node 0) + f (e13Node 1) := by
  unfold e13Node
  unfold e13₀ at f ⊢
  rw [sum_decNode_chance, Fin.sum_univ_two, sum_decNode_decision, sum_decNode_decision]
  have e : ∀ (i : Fin 2) (md : Bool), (∑ q, f ⟨i, some ⟨md, q⟩⟩) = 0 := by
    intro i md
    apply Finset.sum_eq_zero
    intro q _
    cases md
    · unfold e13Forced kBlock slLeaf at q
      rcases q with ⟨fc, ⟨j, e⟩⟩; exact e.elim
    · unfold kBlock slLeaf at q
      rcases q with ⟨j, e⟩; exact e.elim
  simp only [e, Finset.sum_const_zero, add_zero]

/-- The edge payoff masses at the `d`-node of branch `i` under `C(d) = ½`: smoke
`¼(1000 − 10⁶ γ_ℓ)`, refrain `¼(1000 c_ℓ − 10⁶ γ_ℓ)`.
Source: none: infrastructure. Kind: L -/
theorem e13_edgePay (i : Fin 2) :
    (∑ ℓ, if edgeOf e13₀ (e13Node i) ℓ = some true then
      leafLaw e13Half e13₀ ℓ * payoff e13₀ ℓ else 0) =
      1/4 * (1000 - 1000000 * (if i = 0 then 99/100 else 1/100)) ∧
    (∑ ℓ, if edgeOf e13₀ (e13Node i) ℓ = some false then
      leafLaw e13Half e13₀ ℓ * payoff e13₀ ℓ else 0) =
      1/4 * (1000 * (if i = 0 then 9/10 else 1/10) - 1000000 * (if i = 0 then 99/100 else 1/100)) := by
  constructor <;>
  · rw [e13_sum]
    simp only [Fin.sum_univ_two, e13_edgeOf.1, e13_edgeOf.2, e13_leafLaw_smoke, e13_leafLaw_refrain,
      e13_payoff.1, e13_payoff.2, ticklePay, procBool, FinDistr.bool_true, FinDistr.bool_false]
    fin_cases i <;> simp <;> norm_num

/-- The forcing masses on E13 at `C(d) = ½`: `forcedBelow_{q_ℓ}(smoke) = ½(1000 − 10⁶ γ_ℓ)`,
`forcedBelow_{q_ℓ}(refrain) = ½(1000 c_ℓ − 10⁶ γ_ℓ)`.
Source: [[decision-problems-v2]] §8 (`R_q G_q`); mandate T4(c)
Kind: L -/
theorem e13_forcedBelow (i : Fin 2) :
    forcedBelow e13₀ (NodePolicy.ofProc e13Half e13₀) (e13Node i) true =
      1/2 * (1000 - 1000000 * (if i = 0 then 99/100 else 1/100)) ∧
    forcedBelow e13₀ (NodePolicy.ofProc e13Half e13₀) (e13Node i) false =
      1/2 * (1000 * (if i = 0 then 9/10 else 1/10) - 1000000 * (if i = 0 then 99/100 else 1/100)) := by
  obtain ⟨hs, hr⟩ := e13_edgePay i
  have h1 := edge_paySum_eq_mul_forcedBelow e13Half e13₀ (e13Node i) true
  have h2 := edge_paySum_eq_mul_forcedBelow e13Half e13₀ (e13Node i) false
  rw [hs] at h1; rw [hr] at h2
  have hw : ∀ a, (e13Half (pt e13₀ (e13Node i))).w a = 1/2 := by
    intro a; cases a <;> norm_num [procBool]
  rw [hw] at h1 h2
  constructor <;> linarith

/-- `R_{q_ℓ} = ½` on E13. Source: none: infrastructure. Kind: L -/
theorem e13_reach (i : Fin 2) : reach e13Half e13₀ (e13Node i) = 1/2 := by
  unfold e13Node e13₀
  simp only [reach_chance, reach_decision_none, Lesion.coinL, Lesion.fdt, FinDistr.coin]
  fin_cases i <;> simp <;> norm_num

/-- No `d`-node of E13 is a.s. node-action-veridical at `C(d) = ½`: below each, the forced run
"drew refrain, override fired" has positive mass and world `m = 1`.
Source: mandate T4(c) ("`r2Real` **undefined**: no node-action-veridical node")
Kind: L -/
theorem e13_not_nav (i : Fin 2) : ¬ NodeActionVeridicalAS slActEv e13Half e13₀ (e13Node i) := by
  intro h
  have hpos : 0 < leafLaw e13Half e13₀ ⟨i, false, 0, 0, ()⟩ := by
    rw [e13_leafLaw_refrain]; fin_cases i <;> norm_num [procBool]
  have := h ⟨i, false, 0, 0, ()⟩ false hpos (by rw [e13_edgeOf.2]; simp)
  rw [e13_world.2] at this
  simp [slActEv, evM] at this

/-- **R2-real is undefined on E13**: the averaging set is empty (both readings).
Source: mandate T4(c) ("state it as `fiber-of-veridical-nodes = ∅`, kind `N−` for the
referent")
Kind: N− -/
theorem e13_realFiber_empty :
    realFiber slObs slActEv e13Half e13₀ () = ∅ ∧ realFiberAll slActEv e13Half e13₀ () = ∅ := by
  constructor
  · ext q
    rw [mem_realFiber]
    simp only [Finset.notMem_empty, iff_false, not_and]
    obtain ⟨i, rfl⟩ := e13_nodes_cases q
    intro _ h; exact absurd h (e13_not_nav i)
  · ext q
    rw [mem_realFiberAll]
    simp only [Finset.notMem_empty, iff_false, not_and]
    obtain ⟨i, rfl⟩ := e13_nodes_cases q
    intro _ h; exact e13_not_nav i h

/-- **The verdicts on E13 at `C(d) = ½`**: evidential `V(smoke) = −1 889 000/3 < −108 000 =
V(refrain)` at the strictly calibrated state (both acts in `A_d^+`: EDT refrains, non-vacuously);
R1-state `(−499 000, −499 500)` (label-free; `𝔼_{μ_{δ_smoke}}[r]` and `𝔼_{μ_{δ_refrain}}[r]`)
smokes; R2-SIA `(−499 000, −499 500)` over `∑_q R_q = 1` smokes. The textbook contrast is
well-defined at this calibrated state — at a point that is covered but not recorded.
Source: `sl-defensible-claims.md` S2 (R-b), `sl-synthesis.md` §1.1 (Compulsion row: "approved
labels … while deviation, forcing … smoke"); mandate T4(c) (`−629 666.7` vs `−108 000`;
`−499 000` vs `−499 500`)
Kind: N+ -/
theorem e13_verdicts :
    let s₀ : Unit → State TickleW ℚ :=
      fun _ => calibratedState e13Half e13₀ Finset.univ (nu_univ_pos _ _)
    ((s₀ ()).V (evM true) = -1889000/3 ∧ (s₀ ()).V (evM false) = -108000 ∧
      true ∈ APlus s₀ slActEv () ∧ false ∈ APlus s₀ slActEv ()) ∧
    (r1StateVal slObs e13Half e13₀ () true = -499000 ∧
      r1StateVal slObs e13Half e13₀ () false = -499500) ∧
    (r2Sia e13Half e13₀ () true = -499000 ∧ r2Sia e13Half e13₀ () false = -499500 ∧
      fiberMass e13Half e13₀ () = 1) := by
  intro s₀
  obtain ⟨hn1, -, hn3, -⟩ := e13_nu_values e13Half
  obtain ⟨hp1, hp3⟩ := e13_paySum_values e13Half
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · simp only [s₀, calibratedState_V, Finset.inter_univ]
    rw [hp1, hn1]; norm_num [procBool]
  · simp only [s₀, calibratedState_V, Finset.inter_univ]
    rw [hp3, hn3]; norm_num [procBool]
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, s₀,
      calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
    rw [hn1]; norm_num [procBool]
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, s₀,
      calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
    rw [hn3]; norm_num [procBool]
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    have hdev : e13Half.deviatePure () true = fun _ => FinDistr.pure true := by
      rw [Proc.deviatePure, deviate_unit]
    rw [hdev, paySum_eq_sum_ite, e13_sum]
    simp only [Fin.sum_univ_two, e13_leafLaw_smoke, e13_leafLaw_refrain, e13_payoff.1,
      e13_payoff.2, Finset.mem_univ, if_true, FinDistr.pure_w, ticklePay]
    norm_num
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    have hdev : e13Half.deviatePure () false = fun _ => FinDistr.pure false := by
      rw [Proc.deviatePure, deviate_unit]
    rw [hdev, paySum_eq_sum_ite, e13_sum]
    simp only [Fin.sum_univ_two, e13_leafLaw_smoke, e13_leafLaw_refrain, e13_payoff.1,
      e13_payoff.2, Finset.mem_univ, if_true, FinDistr.pure_w, ticklePay]
    norm_num
  · unfold r2Sia
    rw [e13_fiber, e13_sum_decNode]
    simp only [dite_true, transport_const, (e13_forcedBelow 0).1, (e13_forcedBelow 1).1]
    norm_num
  · unfold r2Sia
    rw [e13_fiber, e13_sum_decNode]
    simp only [dite_true, transport_const, (e13_forcedBelow 0).2, (e13_forcedBelow 1).2]
    norm_num
  · unfold fiberMass
    rw [e13_fiber, e13_sum_decNode, e13_reach, e13_reach]; norm_num

end e13

/-! ## (d) Recording the draw dissolves E13 -/

section e13Rec

/-- Worlds `(ℓ, m, k, m_d)`: the lesion algebra enriched by the draw coordinate.
Source: `sl_zoo.py` line 719 (`record_draw=True` "adds the decision coordinate `md`"); Q1's
relativity to the algebra
Kind: D -/
abbrev E13RecW : Type := TickleW × Bool

/-- `O_d = ⊤` on the enriched algebra. Source: dp-core-046. Kind: D -/
def e13RecObs : Unit → Finset E13RecW := fun _ => Finset.univ

/-- The action events `{m_d = ·}` on the enriched algebra. Source: dp-core-046. Kind: D -/
def e13RecActEv : Unit → Bool → Finset E13RecW := fun _ a => Finset.univ.filter fun w => w.2 = a

/-- A leaf of the enriched tree: world `((ℓ, m, k), m_d)`, payoff `α m − β k`.
Source: dp-core-046
Kind: D -/
def e13RecLeaf (ℓ m k md : Bool) : Tree E13RecW Unit (fun _ => Bool) ℚ :=
  .leaf ((ℓ, m, k), md) (ticklePay 1000 1000000 (ℓ, m, k))

/-- The cancer block on the enriched algebra. Source: dp-core-046. Kind: D -/
def e13RecK (i : Fin 2) (m md : Bool) : Tree E13RecW Unit (fun _ => Bool) ℚ :=
  .chance 2 (Lesion.fdt.coinK (decide (i = 0))) fun j => e13RecLeaf (decide (i = 0)) m (decide (j = 0)) md

/-- The compulsion block after a drawn refusal, on the enriched algebra.
Source: dp-core-046
Kind: D -/
def e13RecForced (i : Fin 2) : Tree E13RecW Unit (fun _ => Bool) ℚ :=
  .chance 2 (Compulsion.e13Rates.coinF (decide (i = 0))) fun j => e13RecK i (decide (j = 0)) false

/-- **E13 with the draw recorded** (`e13'`): the same tree as `e13₀`, worlds `((ℓ, m, k), m_d)`.
Source: dp-core-046 ("recording the draw as a coordinate dissolves it"); `sl_zoo.py`
`record_draw=True`; mandate T4(d)
Kind: D
Fidelity: variant: enriched algebra (Q1's relativity), disclosed -/
def e13Rec : Tree E13RecW Unit (fun _ => Bool) ℚ :=
  .chance 2 Lesion.fdt.coinL fun i =>
    .decision () fun md => cond md (e13RecK i true true) (e13RecForced i)

/-- A sum over the leaves of `e13Rec`. Source: none: infrastructure. Kind: L -/
theorem e13Rec_sum (f : e13Rec.Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ j : Fin 2, f ⟨i, true, j, ()⟩) +
      ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩) := by
  unfold e13Rec at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Fintype.sum_bool]
  have h1 : (∑ ℓ, f ⟨i, true, ℓ⟩) = ∑ j : Fin 2, f ⟨i, true, j, ()⟩ := by
    show (∑ ℓ : (e13RecK i true true).Leaves, f ⟨i, true, ℓ⟩) = _
    unfold e13RecK e13RecLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  have h2 : (∑ ℓ, f ⟨i, false, ℓ⟩) = ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩ := by
    show (∑ ℓ : (e13RecForced i).Leaves, f ⟨i, false, ℓ⟩) = _
    unfold e13RecForced e13RecK e13RecLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun fc _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  rw [h1, h2]

/-- The leaf masses of `e13Rec` (same as `e13₀`'s). Source: Definition 6. Kind: L -/
theorem e13Rec_leafLaw (C : Proc Unit (fun _ => Bool) ℚ) :
    (∀ (i j : Fin 2), leafLaw C e13Rec ⟨i, true, j, ()⟩ =
      (1/2 : ℚ) * (C ()).w true *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100))) ∧
    (∀ (i fc j : Fin 2), leafLaw C e13Rec ⟨i, false, fc, j, ()⟩ =
      (1/2 : ℚ) * (C ()).w false *
        (if i = 0 then (if fc = 0 then 9/10 else 1/10) else (if fc = 0 then 1/10 else 9/10)) *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100))) := by
  constructor
  · intro i j
    unfold e13Rec
    rw [leafLaw_chance, leafLaw_decision]
    show (Lesion.fdt.coinL).w i * ((C ()).w true * leafLaw C (e13RecK i true true) ⟨j, ()⟩) = _
    unfold e13RecK e13RecLeaf
    simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, FinDistr.coin, tickleGamma,
      Lesion.fdt]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · intro i fc j
    unfold e13Rec
    rw [leafLaw_chance, leafLaw_decision]
    show (Lesion.fdt.coinL).w i * ((C ()).w false * leafLaw C (e13RecForced i) ⟨fc, j, ()⟩) = _
    unfold e13RecForced e13RecK e13RecLeaf
    simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, Compulsion.coinF,
      FinDistr.coin, tickleGamma, Lesion.fdt, Compulsion.e13Rates]
    fin_cases i <;> fin_cases fc <;> fin_cases j <;> simp <;> ring

/-- The worlds and payoffs at the leaves of `e13Rec`. Source: none: infrastructure. Kind: L -/
theorem e13Rec_world_payoff :
    (∀ (i j : Fin 2), world e13Rec ⟨i, true, j, ()⟩ = ((decide (i = 0), true, decide (j = 0)), true) ∧
      payoff e13Rec ⟨i, true, j, ()⟩ = ticklePay 1000 1000000 (decide (i = 0), true, decide (j = 0))) ∧
    (∀ (i fc j : Fin 2),
      world e13Rec ⟨i, false, fc, j, ()⟩ = ((decide (i = 0), decide (fc = 0), decide (j = 0)), false) ∧
      payoff e13Rec ⟨i, false, fc, j, ()⟩ =
        ticklePay 1000 1000000 (decide (i = 0), decide (fc = 0), decide (j = 0))) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- Every leaf of `e13Rec` is one of the twelve. Source: none: infrastructure. Kind: L -/
theorem e13Rec_leaves (ℓ : e13Rec.Leaves) :
    (∃ (i j : Fin 2), ℓ = ⟨i, true, j, ()⟩) ∨ (∃ (i fc j : Fin 2), ℓ = ⟨i, false, fc, j, ()⟩) := by
  unfold e13Rec e13RecForced e13RecK e13RecLeaf at ℓ
  rcases ℓ with ⟨i, md, ℓ⟩
  cases md
  · rcases ℓ with ⟨fc, j, ⟨⟩⟩; exact Or.inr ⟨i, fc, j, rfl⟩
  · rcases ℓ with ⟨j, ⟨⟩⟩; exact Or.inl ⟨i, j, rfl⟩

/-- Every decision node of `e13Rec` is a `d`-node `⟨i, none⟩`. Source: none: infrastructure. Kind: L -/
theorem e13Rec_nodes_cases (q : e13Rec.DecNode) : ∃ i : Fin 2, q = (⟨i, none⟩ : e13Rec.DecNode) := by
  unfold e13Rec e13RecForced e13RecK e13RecLeaf at q
  rcases q with ⟨i, (_ | ⟨md, q⟩)⟩
  · exact ⟨i, rfl⟩
  · exfalso
    cases md
    · rcases q with ⟨fc, ⟨j, e⟩⟩; exact e.elim
    · rcases q with ⟨j, e⟩; exact e.elim

/-- The edges at the `d`-nodes of `e13Rec`. Source: none: infrastructure. Kind: L -/
theorem e13Rec_edgeOf :
    (∀ (i i' j : Fin 2), edgeOf e13Rec (⟨i, none⟩ : e13Rec.DecNode) ⟨i', true, j, ()⟩ =
      if i' = i then some true else none) ∧
    (∀ (i i' fc j : Fin 2), edgeOf e13Rec (⟨i, none⟩ : e13Rec.DecNode) ⟨i', false, fc, j, ()⟩ =
      if i' = i then some false else none) := by
  constructor
  · intro i i' j
    unfold e13Rec
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance, edgeOf_decision_none]
    · simp [edgeOf_chance, h]
  · intro i i' fc j
    unfold e13Rec
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance, edgeOf_decision_none]
    · simp [edgeOf_chance, h]

/-- Every run of `e13Rec` meets `d` once. Source: none: infrastructure. Kind: L -/
theorem e13Rec_count (ℓ : e13Rec.Leaves) : count () e13Rec ℓ = 1 := by
  rcases e13Rec_leaves ℓ with ⟨i, j, rfl⟩ | ⟨i, fc, j, rfl⟩ <;> · unfold e13Rec; rfl

/-- **`e13Rec` records at `d` for every procedure**: on the enriched algebra the action event
`{m_d = a}` is the draw at the unique `d`-node of the run.
Source: dp-core-046 ("recording the draw as a coordinate dissolves it"); mandate T4(d)
Kind: N+ -/
theorem e13Rec_recordsFor (C : Proc Unit (fun _ => Bool) ℚ) :
    RecordsFor e13RecObs e13RecActEv C e13Rec () := by
  intro ℓ _ _
  refine ⟨e13Rec_count ℓ, ?_⟩
  intro q hq a ha
  obtain ⟨i, rfl⟩ := e13Rec_nodes_cases q
  rcases e13Rec_leaves ℓ with ⟨i', j, rfl⟩ | ⟨i', fc, j, rfl⟩
  · rw [e13Rec_edgeOf.1] at ha
    by_cases h : i' = i
    · subst h
      simp only [if_true, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => Finset.mem_univ _, ?_, ?_⟩
      · rw [(e13Rec_world_payoff.1 i' j).1]; simp [e13RecActEv]
      · intro a' ha'; rw [(e13Rec_world_payoff.1 i' j).1] at ha'; simp [e13RecActEv] at ha'
        exact ha'
    · simp [h] at ha
  · rw [e13Rec_edgeOf.2] at ha
    by_cases h : i' = i
    · subst h
      simp only [if_true, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => Finset.mem_univ _, ?_, ?_⟩
      · rw [(e13Rec_world_payoff.2 i' fc j).1]; simp [e13RecActEv]
      · intro a' ha'; rw [(e13Rec_world_payoff.2 i' fc j).1] at ha'; simp [e13RecActEv] at ha'
        exact ha'
    · simp [h] at ha

/-- **The act values on `e13Rec` are `(−499 000, −499 500)`**: for every procedure,
`paySum(m_d = 1) = −499 000 · ν(m_d = 1)` and `paySum(m_d = 0) = −499 500 · ν(m_d = 0)`, with
`ν(m_d = a) = C(d)(a)`; so at every strictly calibrated state with both draws possible,
`V(m_d = 1) = −499 000 > −499 500 = V(m_d = 0)` (smoke), and the conditionals of cancer on the
draw are flat (`e13Rec_recordsFor` + `nuFlat_of_recordsFor_postQueryIndep` would give them; here
the values are computed).
Source: dp-core-046 ("`V(m_d = 1) = −499 000 > −499 500 = V(m_d = 0)`"); mandate T4(d)
Kind: P
Fidelity: variant: enriched algebra
Hyps: none -/
theorem e13Rec_values (C : Proc Unit (fun _ => Bool) ℚ) :
    nu C e13Rec (e13RecActEv () true) = (C ()).w true ∧
    nu C e13Rec (e13RecActEv () false) = (C ()).w false ∧
    paySum C e13Rec (e13RecActEv () true) = -499000 * (C ()).w true ∧
    paySum C e13Rec (e13RecActEv () false) = -499500 * (C ()).w false := by
  obtain ⟨hs, hr⟩ := e13Rec_leafLaw C
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, e13Rec_sum]
    simp only [Fin.sum_univ_two, hs, hr, (e13Rec_world_payoff.1 _ _).1, (e13Rec_world_payoff.2 _ _ _).1,
      e13RecActEv, Finset.mem_filter, Finset.mem_univ, true_and]
    simp; ring
  · rw [nu_eq_sum, e13Rec_sum]
    simp only [Fin.sum_univ_two, hs, hr, (e13Rec_world_payoff.1 _ _).1, (e13Rec_world_payoff.2 _ _ _).1,
      e13RecActEv, Finset.mem_filter, Finset.mem_univ, true_and]
    simp; ring
  · rw [paySum_eq_sum_ite, e13Rec_sum]
    simp only [Fin.sum_univ_two, hs, hr, (e13Rec_world_payoff.1 _ _).1, (e13Rec_world_payoff.1 _ _).2,
      (e13Rec_world_payoff.2 _ _ _).1, (e13Rec_world_payoff.2 _ _ _).2, e13RecActEv,
      Finset.mem_filter, Finset.mem_univ, true_and, ticklePay]
    simp; ring
  · rw [paySum_eq_sum_ite, e13Rec_sum]
    simp only [Fin.sum_univ_two, hs, hr, (e13Rec_world_payoff.1 _ _).1, (e13Rec_world_payoff.1 _ _).2,
      (e13Rec_world_payoff.2 _ _ _).1, (e13Rec_world_payoff.2 _ _ _).2, e13RecActEv,
      Finset.mem_filter, Finset.mem_univ, true_and, ticklePay]
    simp; ring

/-- **Recording the draw dissolves E13** at the strict grade: at `C(d) = ½` the strictly
calibrated state on `e13Rec` has both draws subjectively possible and
`V(m_d = 1) = −499 000 > −499 500 = V(m_d = 0)`: it smokes, and the tree records.
Source: dp-core-046; mandate T4(d)
Kind: N+
Fidelity: variant: enriched algebra -/
theorem prop14_e13_recorded_draw_dissolves :
    let s₀ : Unit → State E13RecW ℚ :=
      fun _ => calibratedState e13Half e13Rec Finset.univ (nu_univ_pos _ _)
    RecordsFor e13RecObs e13RecActEv e13Half e13Rec () ∧ StrictOCAt s₀ e13RecObs e13Half e13Rec () ∧
      (s₀ ()).V (e13RecActEv () true) = -499000 ∧ (s₀ ()).V (e13RecActEv () false) = -499500 ∧
      true ∈ APlus s₀ e13RecActEv () ∧ false ∈ APlus s₀ e13RecActEv () := by
  intro s₀
  obtain ⟨h1, h2, h3, h4⟩ := e13Rec_values e13Half
  refine ⟨e13Rec_recordsFor _, strictOCAt_calibratedState e13RecObs _ _ s₀ () _ rfl, ?_, ?_, ?_, ?_⟩
  · simp only [s₀, calibratedState_V, Finset.inter_univ]
    rw [h3, h1]; norm_num [procBool]
  · simp only [s₀, calibratedState_V, Finset.inter_univ]
    rw [h4, h2]; norm_num [procBool]
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, s₀, calibratedState_pr,
      Finset.inter_univ, nu_univ, div_one]
    rw [h1]; norm_num [procBool]
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, s₀, calibratedState_pr,
      Finset.inter_univ, nu_univ, div_one]
    rw [h2]; norm_num [procBool]

end e13Rec

end Cleanroom.Decision.DpSmokingLesion
