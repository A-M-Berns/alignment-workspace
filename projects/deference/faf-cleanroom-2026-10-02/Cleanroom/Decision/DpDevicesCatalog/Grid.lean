import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpDevicesCatalog.Remark314
import Cleanroom.Decision.DpDevicesCatalog.TableMugging
import Cleanroom.Decision.DpDevicesCatalog.AmdDevices
import Cleanroom.Decision.DpCalibration.Miniature
import Cleanroom.Decision.DpCalibration.MiniDevices

set_option autoImplicit false

/-!
# `dp-devices-catalog` — the extension (the vacuity criterion) and T9 (the three-valued grid)

**The vacuity criterion** (`d2VacuousAt_iff`, `d2VacuousAt_eps_free`): D2's escape clause
fires at `d` under `C^ε` — no action event is realized within `O_d` — iff no chance-positive
leaf has its world in any `a ∧ O_d`; this is a property of the tree and the events alone,
independent of `C` and of `ε` (a full-support tremble gives every chance-positive leaf positive
mass). Corollaries: with unrealised action events *every* procedure is D2-consistent
(`eventTremble_of_unrealised`) — the dryness finding: "the AMD is event-tremble-EDT-consistent
at every `q`" (`amd_unrec_eventTremble`) was vacuous. The analogue for the guarded strict sense
(`strictOCAt_vacuous_iff`): `StrictOCAt` is vacuous at `d` iff no positive-mass leaf lies in
`O_d`, a property of `(B, C)`.

**T9**: `Verdict` (`T`/`T*`/`vac`/`F`) and ZO-19's reading rule `GridVerdict` over the queried
points, with rows proven exactly as the grid prints them: `Told-You-So, C₀` (strict `T*`,
limit `T`, `T_EDT` `T`, trembleEDT `T`), `Told-You-So, C*` (strict `T*`, limit `T`, `T_EDT` `F`,
trembleEDT `F`), `Remark 4.3 miniature, q = 2/3` (strict `T`, limit `T`, `T_EDT` `T`,
trembleEDT `F`), `B₁ no-doubt mugging, C = pay` (all seven columns: `F, T, F, F, F, F, F`), and
the AMD under the unrecorded encoding (trembleEDT `vac` at every `q`). The masked / per-run /
per-occurrence cells of the Told-You-So and miniature rows are in `GridMore` (all seven columns
of those three rows are shipped).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## The verdict type and ZO-19's reading rule -/

/-- ZO-19's three-valued verdicts (plus `F`): `T` substantively true at every queried point,
`T*` no violation with some queried point vacuous, `vac` every queried point vacuous, `F` a
violation.
Source: `zoo.md` ZO-19 ("Reading rule (binding for downstream use)")
Kind: D -/
inductive Verdict : Type
  | T
  | Tstar
  | vac
  | F
  deriving DecidableEq

/-- **ZO-19's reading rule** for one column over the queried points `Q`, given the per-point
"no violation" predicate `ok` and the per-point "vacuous" predicate `vac`.
Source: `zoo.md` ZO-19 (line 133)
Kind: D
Fidelity: exact (`T*` requires some substantive point, so that `vac` and `T*` are disjoint) -/
def GridVerdict {ι : Type} (Q : Finset ι) (ok vac : ι → Prop) : Verdict → Prop
  | .T => ∀ d ∈ Q, ok d ∧ ¬ vac d
  | .Tstar => (∀ d ∈ Q, ok d) ∧ (∃ d ∈ Q, vac d) ∧ (∃ d ∈ Q, ¬ vac d)
  | .vac => ∀ d ∈ Q, vac d
  | .F => ∃ d ∈ Q, ¬ ok d

section criterion

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℚ)
  (C : Proc ι acts ℚ)

/-- The body of D2 at one point `d` for the tremble size `ε` (`D2At` is this at every queried
point).
Source: `calibration.md` Devices (D2); `dynamic.md` DY-3
Kind: D -/
def D2BodyAt (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ι) : Prop :=
  nuPoly C B (obs d) ≠ 0 →
    (∃ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d)) → ∀ a, 0 < (C d).w a →
    0 < nu (tremble C ε h0.le h1) B (actEv d a ∩ obs d) ∧
    ∀ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) →
      condExp (tremble C ε h0.le h1) B (actEv d b ∩ obs d) ≤
        condExp (tremble C ε h0.le h1) B (actEv d a ∩ obs d)

/-- `D2At` is the body at every queried point. Source: none: infrastructure. Kind: L -/
theorem d2At_iff (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    D2At obs actEv B C ε h0 h1 ↔ ∀ d ∈ queried B, D2BodyAt obs actEv B C ε h0 h1 d :=
  Iff.rfl

/-- **D2's escape clause fires at `d` under `C^ε`**: no action event is realized within `O_d`.
Source: [[decision-problems-v2]] §4 Definition 18 ("no constraint where `A_d^+ = ∅`");
mandate extension
Kind: D -/
def D2VacuousAt (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ι) : Prop :=
  ∀ b, nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) = 0

/-- A vacuous point satisfies the body (the escape clause discharges it).
Source: mandate extension
Kind: L -/
theorem D2VacuousAt.body {ε : ℚ} {h0 : 0 < ε} {h1 : ε ≤ 1} {d : ι}
    (h : D2VacuousAt obs actEv B C ε h0 h1 d) : D2BodyAt obs actEv B C ε h0 h1 d := by
  intro _ ⟨b, hb⟩
  rw [h b] at hb
  exact absurd hb (lt_irrefl 0)

/-- `ν_C(Y) = 0` iff no positive-mass leaf has its world in `Y`.
Source: none: infrastructure
Kind: L -/
theorem nu_eq_zero_iff (Y : Finset Ω) :
    nu C B Y = 0 ↔ ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∉ Y := by
  unfold nu mass
  rw [Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ]
  constructor
  · intro h ℓ hpos hw
    have := h ℓ (by simp [worldEv, hw])
    rw [this] at hpos; exact lt_irrefl 0 hpos
  · intro h ℓ hℓ
    rw [worldEv, Finset.mem_filter] at hℓ
    by_contra hne
    exact h ℓ (lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hne)) hℓ.2

/-- **The vacuity criterion, one `ε`**: under `C^ε` (`0 < ε ≤ 1`) the escape clause fires at
`d` iff no chance-positive leaf has its world in any `a ∧ O_d` — a property of `(B, obs,
actEv)` alone. (A full-support tremble gives every chance-positive leaf positive mass, and a
chance-null leaf has mass `0` under every procedure.)
Source: mandate extension ("`d2At_vacuous_iff`"); `zoo.md` ZO-19 (the 19 vacuous cells)
Kind: P
Fidelity: exact
Hyps: none -/
theorem d2VacuousAt_iff (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ι) :
    D2VacuousAt obs actEv B C ε h0 h1 d ↔
      ∀ a, ∀ ℓ, Positive B ℓ → world B ℓ ∉ actEv d a ∩ obs d := by
  constructor
  · intro h a ℓ hℓ hw
    have := nu_pos_of_leaf_fullSupport (tremble_fullSupport C ε h0 h1) B _ ℓ hw hℓ
    rw [h a] at this
    exact lt_irrefl 0 this
  · intro h a
    rw [nu_eq_zero_iff]
    intro ℓ hpos hw
    apply h a ℓ _ hw
    rw [leafLaw_eq_chanceWeight_mul_drawsWeight] at hpos
    rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hc | hc
    · exact hc
    · rw [← hc, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)

/-- **The vacuity criterion, `ε`-free**: the escape clause fires at `d` for all sufficiently
small `ε` iff it fires for every `ε ∈ (0, 1]` iff no chance-positive leaf has its world in any
`a ∧ O_d`.
Source: mandate extension
Kind: C
Fidelity: exact
Hyps: none -/
theorem d2VacuousAt_eps_free (d : ι) :
    (∃ ε₀ > (0 : ℚ), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      D2VacuousAt obs actEv B C ε h0 h1 d) ↔
    ∀ a, ∀ ℓ, Positive B ℓ → world B ℓ ∉ actEv d a ∩ obs d := by
  constructor
  · rintro ⟨ε₀, hε₀, h⟩
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have e0 : 0 < min ε₀ 1 / 2 := by linarith
    have e1 : min ε₀ 1 / 2 ≤ 1 := by linarith [min_le_right ε₀ 1]
    have hlt : min ε₀ 1 / 2 < ε₀ := by linarith [min_le_left ε₀ 1]
    exact (d2VacuousAt_iff obs actEv B C _ e0 e1 d).mp (h _ e0 e1 hlt)
  · intro h
    exact ⟨1, one_pos, fun ε h0 h1 _ => (d2VacuousAt_iff obs actEv B C ε h0 h1 d).mpr h⟩

/-- **The dryness finding as a theorem**: if no queried point has a chance-positive leaf-world
in any `a ∧ O_d`, then *every* procedure is D2-consistent — vacuously.
Source: `zoo.md` ZO-19 ("`trembleEDT` column vacuous in 19/74 rows … recorded as
*unconstrained* by event-tremble-EDT, never as consistent")
Kind: C
Fidelity: exact
Hyps: (a) the unrealised-events hypothesis -/
theorem eventTremble_of_unrealised
    (h : ∀ d ∈ queried B, ∀ a, ∀ ℓ, Positive B ℓ → world B ℓ ∉ actEv d a ∩ obs d) :
    EventTrembleEdtConsistent obs actEv C B :=
  ⟨1, one_pos, fun ε h0 h1 _ d hd =>
    ((d2VacuousAt_iff obs actEv B C ε h0 h1 d).mpr (h d hd)).body⟩

/-- **The guarded strict sense is vacuous at `d` iff no positive-mass leaf lies in `O_d`** (a
property of `(B, C)`), and then any state is strictly calibrated at `d`.
Source: mandate extension ("the analogue for the guarded senses")
Kind: L -/
theorem strictOCAt_vacuous_iff (d : ι) :
    nu C B (obs d) = 0 ↔ ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∉ obs d :=
  nu_eq_zero_iff B C (obs d)

/-- A null observation makes every state strictly calibrated at `d`.
Source: [[decision-problems-v2]] Definition 8 ("Queried points with `ν(O_d) = 0` are
unconstrained")
Kind: L -/
theorem strictOCAt_of_vacuous (s : ι → State Ω ℚ) (d : ι) (h : nu C B (obs d) = 0) :
    StrictOCAt s obs C B d := fun hpos => by rw [h] at hpos; exact absurd hpos (lt_irrefl 0)

end criterion

/-! ## The AMD under the unrecorded encoding: the flagship vacuous cell -/

/-- The grid's unrecorded action-event encoding of the AMD: no leaf-world lies in any action
event (rendered as the empty events; any events disjoint from `{sa, sba, sbb}` behave alike by
`d2VacuousAt_iff`).
Source: `zoo.md` ZO-19 (the AMD rows: `trembleEDT = vac`); mandate T9
Kind: D
Fidelity: variant: the unrecorded encoding rendered as empty action events -/
def amdActEvUnrec : Unit → Act2 → Finset AmdW := fun _ _ => ∅

/-- Under the unrecorded encoding D2's escape clause fires at every `q`, every `ε`.
Source: `zoo.md` ZO-19
Kind: L -/
theorem amd_unrec_d2Vacuous (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    D2VacuousAt amdObs amdActEvUnrec amd (procQ q hq0 hq1) ε h0 h1 () := by
  intro b; simp [amdActEvUnrec]

/-- **"The AMD is event-tremble-EDT-consistent at every `q`" — vacuously**: under the
unrecorded encoding every procedure is D2-consistent, by the escape clause alone.
Source: `zoo.md` ZO-19 (the dryness finding: nineteen phase-1 "T" cells were vacuous, the AMD
rows the flagship)
Kind: N− (the content is that there is none)
Fidelity: exact -/
theorem amd_unrec_eventTremble (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    EventTrembleEdtConsistent amdObs amdActEvUnrec (procQ q hq0 hq1) amd :=
  eventTremble_of_unrealised _ _ _ _ fun _ _ _ _ _ => by simp [amdActEvUnrec]

/-- **Grid row `AMD, any q`: trembleEDT = `vac`**, at every `ε`.
Source: `zoo.md` ZO-19 (rows "AMD, q=1/3", "AMD, q=0 (δ_b)", "AMD, q=1/4", "AMD, q=1/2")
Kind: T
Fidelity: exact -/
theorem grid_amd_unrec_vac (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    GridVerdict (queried amd) (D2BodyAt amdObs amdActEvUnrec amd (procQ q hq0 hq1) ε h0 h1)
      (D2VacuousAt amdObs amdActEvUnrec amd (procQ q hq0 hq1) ε h0 h1) .vac :=
  fun d _ => by cases d; exact amd_unrec_d2Vacuous q ε hq0 hq1 h0 h1

/-! ## Told-You-So rows -/

/-- `ν_{C₀}(O₅) = 1`, `ν_{C₀}(O₁₀) = 0`; `ν_{C*}(O₅) = 0`, `ν_{C*}(O₁₀) = 1`.
Source: v2 Proposition 8 proof. Kind: L -/
theorem tys_nu_obs_values :
    nu procFiveTen toldYouSo (tysObs .five) = 1 ∧ nu procFiveTen toldYouSo (tysObs .ten) = 0 ∧
    nu procTake10 toldYouSo (tysObs .five) = 0 ∧ nu procTake10 toldYouSo (tysObs .ten) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [tys_nu] <;> simp [tysObs, procFiveTen, procTake10]

/-- **Grid row `Told-You-So, C₀`: strict = `T*`** (calibrated at both points, `O₁₀` null,
`O₅` realized).
Source: `zoo.md` ZO-19 (row "Told-You-So, C0": `T*`)
Kind: T -/
theorem grid_tys_fiveTen_strict :
    GridVerdict (queried toldYouSo) (StrictOCAt tysState tysObs procFiveTen toldYouSo)
      (fun d => nu procFiveTen toldYouSo (tysObs d) = 0) .Tstar := by
  obtain ⟨a, b, -, -⟩ := tys_nu_obs_values
  exact ⟨fun d hd => tys_fiveTen_strictOC d hd, ⟨.ten, tys_queried .ten, b⟩,
    ⟨.five, tys_queried .five, by dsimp only; rw [a]; norm_num⟩⟩

/-- **Grid row `Told-You-So, C*`: strict = `T*`** (`O₅` null, `O₁₀` realized).
Source: `zoo.md` ZO-19 (row "Told-You-So, C*": `T*`)
Kind: T -/
theorem grid_tys_take10_strict :
    GridVerdict (queried toldYouSo) (StrictOCAt tysState tysObs procTake10 toldYouSo)
      (fun d => nu procTake10 toldYouSo (tysObs d) = 0) .Tstar := by
  obtain ⟨-, -, c, d'⟩ := tys_nu_obs_values
  exact ⟨fun d hd => tys_take10_strictOC d hd, ⟨.five, tys_queried .five, c⟩,
    ⟨.ten, tys_queried .ten, by dsimp only; rw [d']; norm_num⟩⟩

/-- **Grid rows `Told-You-So, C₀` and `C*`: limit = `T`** (both observations are
tremble-realizable, both procedures limit-calibrated).
Source: `zoo.md` ZO-19 (rows "Told-You-So, C0" / "C*": limit `T`)
Kind: T -/
theorem grid_tys_limit :
    GridVerdict (queried toldYouSo) (LimitOCAt tysState tysObs procFiveTen toldYouSo)
      (fun d => nuPoly procFiveTen toldYouSo (tysObs d) = 0) .T ∧
    GridVerdict (queried toldYouSo) (LimitOCAt tysState tysObs procTake10 toldYouSo)
      (fun d => nuPoly procTake10 toldYouSo (tysObs d) = 0) .T := by
  constructor <;> intro d hd <;> cases d
  · exact ⟨tys_fiveTen_limitOC _ hd, tys_nuPoly_obs_five_ne_zero _⟩
  · exact ⟨tys_fiveTen_limitOC _ hd, tys_nuPoly_obs_ten_ne_zero _⟩
  · exact ⟨tys_take10_limitOC _ hd, tys_nuPoly_obs_five_ne_zero _⟩
  · exact ⟨tys_take10_limitOC _ hd, tys_nuPoly_obs_ten_ne_zero _⟩

/-- **Grid rows `Told-You-So`: `T_EDT` = `T` for `C₀`, `F` for `C*`** (`A⁺` nonempty at both
points; `C*` plays `ten ∉ A⁺_{d₅}`).
Source: `zoo.md` ZO-19 (rows "Told-You-So, C0": `T`; "C*": `F`)
Kind: T -/
theorem grid_tys_tEdt :
    GridVerdict (queried toldYouSo) (TEdtAt tysState tysActEv procFiveTen)
      (fun d => ¬ (APlus tysState tysActEv d).Nonempty) .T ∧
    GridVerdict (queried toldYouSo) (TEdtAt tysState tysActEv procTake10)
      (fun d => ¬ (APlus tysState tysActEv d).Nonempty) .F := by
  constructor
  · intro d hd
    refine ⟨procFiveTen_limitStateEdt.2 d hd, ?_⟩
    cases d
    · dsimp only; rw [tys_aPlus_five]; simp
    · dsimp only; rw [tys_aPlus_ten]; simp
  · refine ⟨.five, tys_queried .five, fun h => ?_⟩
    have := h (by rw [tys_aPlus_five]; exact ⟨.five, by simp⟩) .ten (by simp [procTake10])
    have hmem := argmaxPlus_subset tysState tysActEv .five this
    rw [tys_aPlus_five] at hmem
    simp at hmem

/-- **Grid rows `Told-You-So`: trembleEDT = `T` for `C₀`, `F` for `C*`**, at every `ε ∈ (0,1]`
(both points substantive: `five ∧ O₅` and `ten ∧ O₁₀` are realized under every tremble).
Source: `zoo.md` ZO-19 (rows "Told-You-So, C0": `T`; "C*": `F`); `dynamic.md` DY-5
Kind: T -/
theorem grid_tys_tremble (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    GridVerdict (queried toldYouSo) (D2BodyAt tysObs tysActEv toldYouSo procFiveTen ε h0 h1)
      (D2VacuousAt tysObs tysActEv toldYouSo procFiveTen ε h0 h1) .T ∧
    GridVerdict (queried toldYouSo) (D2BodyAt tysObs tysActEv toldYouSo procTake10 ε h0 h1)
      (D2VacuousAt tysObs tysActEv toldYouSo procTake10 ε h0 h1) .F := by
  constructor
  · intro d hd
    refine ⟨procFiveTen_d2At ε h0 h1 d hd, fun hvac => ?_⟩
    cases d
    · have := hvac .five
      rw [(tys_tremble_nu_five procFiveTen ε h0.le h1).1] at this
      exact (tys_tremble_w_pos procFiveTen ε h0 h1 _ _).ne' this
    · have := hvac .ten
      rw [(tys_tremble_nu_ten procFiveTen ε h0.le h1).1] at this
      exact (mul_pos (tys_tremble_w_pos procFiveTen ε h0 h1 _ _)
        (tys_tremble_w_pos procFiveTen ε h0 h1 _ _)).ne' this
  · by_contra h
    exact procTake10_not_d2At ε h0 h1 fun d hd =>
      Classical.byContradiction fun hn => h ⟨d, hd, hn⟩

/-! ## The miniature at `q = 2/3` -/

/-- **Grid row `Remark 4.3 miniature, q = 2/3`: strict `T`, limit `T`, `T_EDT` `T`**.
Source: `zoo.md` ZO-19 (row "Remark 4.3 miniature, q=2/3": `T T T T T T F`), the three
observation/advocacy columns shipped
Kind: T -/
theorem grid_miniature_tie :
    GridVerdict (queried miniature)
      (StrictOCAt (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniObs
        (procQ (2/3) (by norm_num) (by norm_num)) miniature)
      (fun d => nu (procQ (2/3) (by norm_num) (by norm_num)) miniature (miniObs d) = 0) .T ∧
    GridVerdict (queried miniature)
      (LimitOCAt (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniObs
        (procQ (2/3) (by norm_num) (by norm_num)) miniature)
      (fun d => nuPoly (procQ (2/3) (by norm_num) (by norm_num)) miniature (miniObs d) = 0) .T ∧
    GridVerdict (queried miniature)
      (TEdtAt (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniActEv
        (procQ (2/3) (by norm_num) (by norm_num)))
      (fun d => ¬ (APlus (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniActEv
        d).Nonempty) .T := by
  have hpos : 0 < nu (procQ (2/3) (by norm_num) (by norm_num)) miniature (miniObs ()) := by
    rw [miniObs, nu_univ]; norm_num
  refine ⟨fun d hd => ⟨miniature_strictOC _ _ _ d hd, ?_⟩, fun d hd => ⟨?_, ?_⟩,
    fun d hd => ⟨?_, ?_⟩⟩
  · cases d; exact hpos.ne'
  · cases d
    exact limitOCAt_of_strictOCAt_of_pos _ miniObs _ miniature () hpos
      (miniature_strictOC _ _ _ () hd)
  · cases d; exact miniature_nuPoly_obs_ne_zero _
  · cases d; exact miniature_tie_approved.2
  · cases d
    intro hne
    apply hne
    rw [miniature_aPlus]
    exact ⟨.a, by simp [procQ]⟩

/-- **Grid row `Remark 4.3 miniature, q = 2/3`: trembleEDT = `F`** at every `ε ∈ (0, 1)`: the
trembled label `q_ε = 2/3 − ε/6 < 2/3` breaks the tie in favour of `a`, and `b` is played.
Source: `zoo.md` ZO-19 (row "Remark 4.3 miniature, q=2/3": trembleEDT `F`); CA-14′
Kind: T -/
theorem grid_miniature_tie_tremble (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) :
    GridVerdict (queried miniature)
      (D2BodyAt miniObs miniActEv miniature (procQ (2/3) (by norm_num) (by norm_num)) ε h0 h1.le)
      (D2VacuousAt miniObs miniActEv miniature (procQ (2/3) (by norm_num) (by norm_num)) ε h0
        h1.le) .F := by
  refine ⟨(), miniature_queried, fun h => ?_⟩
  obtain ⟨hi0, hi1⟩ := qeps_interior (2/3) ε (by norm_num) (by norm_num) h0 h1
  have hlive : ∀ b, 0 < nu (tremble (procQ (2/3) (by norm_num) (by norm_num)) ε h0.le h1.le)
      miniature (miniActEv () b ∩ miniObs ()) := by
    intro b
    rw [tremble_procQ, miniObs, Finset.inter_univ, miniature_nu_live]
    cases b <;> simp [procQ] <;> linarith
  obtain ⟨-, hcmp⟩ := h (miniature_nuPoly_obs_ne_zero _) ⟨.a, hlive .a⟩ .b
    (by simp [procQ]; norm_num)
  have := hcmp .a (hlive .a)
  rw [tremble_procQ] at this
  obtain ⟨va, vb⟩ := miniature_condExp _ hi0 hi1
  rw [va, vb] at this
  linarith

/-! ## The no-doubt mugging with `C = pay`: all seven columns -/

section muggingRow

variable (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)

/-- The no-doubt state's act values: `V(pay) = −x`, `V(refuse) = 0`.
Source: `firstperson.md` FP-2 ("`V_s(ρ_d(pay)) = −x`"); ID-18 ("`𝔼[r ∣ choice = pay] = −x`")
Kind: L -/
theorem mugState1_V_act :
    (mugState1 x y q₀ h0.le h1.le).V (mugActEv () .a) = -x ∧
    (mugState1 x y q₀ h0.le h1.le).V (mugActEv () .b) = 0 := by
  simp only [mugState1, calibratedState_V, mug1_nu, mug1_paySum, mugActEv, mugObs, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  have hq : q₀ ≠ 0 := h0.ne'
  have hq' : 1 - q₀ ≠ 0 := by linarith
  constructor <;> simp <;> field_simp

/-- **Grid row `B₁ no-doubt mugging, C = pay`: `(F, T, F, F, F, F, F)`** — strict `F`
(`q₀ ≠ 1`), masked `T` (substantive: the self-model realizes `O_T`), limit `F`, per-run `F`,
per-occurrence `F`, `T_EDT` `F` (`V(pay) = −x < 0 = V(refuse)`, both acts subjectively
possible), trembleEDT `F` at every `ε`.
Source: `zoo.md` ZO-19 (row "B1 no-doubt mugging, C=pay": `F T F F F F F`)
Kind: T
Fidelity: exact (interior no-doubt label `q₀`; `C = δ_pay`) -/
theorem grid_mug1_pay (hx : 0 < x) (ε : ℚ) (e0 : 0 < ε) (e1 : ε ≤ 1) :
    GridVerdict (queried (mug1 x y))
      (StrictOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ 1 zero_le_one le_rfl)
        (mug1 x y))
      (fun d => nu (procQ 1 zero_le_one le_rfl) (mug1 x y) (mugObs d) = 0) .F ∧
    GridVerdict (queried (mug1 x y))
      (MaskedOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ 1 zero_le_one le_rfl)
        (mug1 x y))
      (fun d => ∀ C', Admissible .LF (procQ 1 zero_le_one le_rfl) d C' →
        nu C' (mug1 x y) (mugObs d) = 0) .T ∧
    GridVerdict (queried (mug1 x y))
      (LimitOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ 1 zero_le_one le_rfl)
        (mug1 x y))
      (fun d => nuPoly (procQ 1 zero_le_one le_rfl) (mug1 x y) (mugObs d) = 0) .F ∧
    GridVerdict (queried (mug1 x y))
      (PerRunSSCAt (fun _ => mugState1 x y q₀ h0.le h1.le) (procQ 1 zero_le_one le_rfl)
        (mug1 x y))
      (fun d => mass (procQ 1 zero_le_one le_rfl) (mug1 x y) (occ d (mug1 x y)) = 0) .F ∧
    GridVerdict (queried (mug1 x y))
      (PerOccSSCAt (fun _ => mugState1 x y q₀ h0.le h1.le) (procQ 1 zero_le_one le_rfl)
        (mug1 x y))
      (fun d => countMass (procQ 1 zero_le_one le_rfl) (mug1 x y) d Finset.univ = 0) .F ∧
    GridVerdict (queried (mug1 x y))
      (TEdtAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugActEv (procQ 1 zero_le_one le_rfl))
      (fun d => ¬ (APlus (fun _ => mugState1 x y q₀ h0.le h1.le) mugActEv d).Nonempty) .F ∧
    GridVerdict (queried (mug1 x y))
      (D2BodyAt mugObs mugActEv (mug1 x y) (procQ 1 zero_le_one le_rfl) ε e0 e1)
      (D2VacuousAt mugObs mugActEv (mug1 x y) (procQ 1 zero_le_one le_rfl) ε e0 e1) .F := by
  have hq : () ∈ queried (mug1 x y) := mug1_queried_mem x y
  have hstrict : ¬ StrictOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs
      (procQ 1 zero_le_one le_rfl) (mug1 x y) () := by
    rw [mug1_strictOC_iff]; linarith
  refine ⟨⟨(), hq, hstrict⟩, fun d _ => ?_, ⟨(), hq, fun h => hstrict
    (limitOCAt_imp_strictOCAt _ mugObs _ (mug1 x y) () h)⟩,
    ⟨(), hq, mug1_not_perRunSSC_all x y q₀ h0.le h1.le _⟩,
    ⟨(), hq, mug1_not_perOccSSC_all x y q₀ h0.le h1.le _⟩, ⟨(), hq, fun h => ?_⟩,
    ⟨(), hq, fun h => ?_⟩⟩
  · cases d
    refine ⟨(mug_maskedOC_all x y q₀ h0 h1 _).1 () hq, fun hvac => ?_⟩
    have := hvac ((procQ 1 zero_le_one le_rfl).deviate () FinDistr.uniform)
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [mug1_nu_obs] at this
    norm_num at this
  · -- `T_EDT` fails: `pay` is played, both acts are in `A⁺`, and `V(refuse) > V(pay)`
    obtain ⟨pa, pb⟩ := mugLimitState_pr x y q₀ h0.le h1.le
    obtain ⟨va, vb⟩ := mugState1_V_act x y q₀ h0 h1
    have hne : (APlus (fun _ => mugState1 x y q₀ h0.le h1.le) mugActEv ()).Nonempty :=
      ⟨.a, by simp [APlus]; show 0 < (mugLimitState x y q₀ h0.le h1.le).pr (mugActEv () .a)
              rw [pa]; exact h0⟩
    have hmem := h hne .a (by simp [procQ])
    rw [mem_argmaxPlus] at hmem
    have hb : Act2.b ∈ APlus (fun _ => mugState1 x y q₀ h0.le h1.le) mugActEv () := by
      simp [APlus]; show 0 < (mugLimitState x y q₀ h0.le h1.le).pr (mugActEv () .b)
      rw [pb]; linarith
    have := hmem.2 .b hb
    rw [va, vb] at this
    linarith
  · -- D2's body fails at `ε`: `pay` is played, `condExp(refuse) = 0 > −x = condExp(pay)`
    have hfs := tremble_fullSupport (procQ 1 zero_le_one le_rfl) ε e0 e1
    obtain ⟨-, hcmp⟩ := h (mug1_nuPoly_obs_ne_zero x y _) ⟨.a, mug1_nu_actObs_pos x y hfs .a⟩ .a
      (by simp [procQ])
    have := hcmp .b (mug1_nu_actObs_pos x y hfs .b)
    obtain ⟨ca, cb⟩ := mug1_tremble_condExp x y _ ε e0 e1
    rw [ca, cb] at this
    linarith

end muggingRow

end Cleanroom.Decision.DpDevicesCatalog
