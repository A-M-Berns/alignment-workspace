import Cleanroom.Lit.LitDdbFacts.ExamplesPrior

/-!
# Audit round 3 (adversarial) probes for `lit-ddb-facts`

Not imported by the library. Elaborated with `scripts/lean-check`.

* **Q1.** On *any* prior frame (no nestedness), Total Trust of the prior forces the evidence to
  be transitive: `v ∈ E_w → E_v ⊆ E_w`. Route: `totalTrust_cands` makes every row totally trust
  the frame, `TotalTrust.simpleTrust` and `positiveAccess_of_simpleTrust` give the row at `w`
  positive access, and positive access at `q = E_w` (of which the row is certain) says every
  world of `E_w` has a row certain of `E_w`, i.e. `E_v ⊆ E_w` by regularity. This is the half of
  the report's "natural converse question" (E1) that the package's own lemmas already give; the
  audit text supplies the other half (transitive + factive + Total Trust ⟹ nested) on paper.
* **Q2.** The antecedent of `PriorFrame.totalTrust_of_nested_of_simpleTrust` is load-bearing and
  `Nested` smuggles no factivity: a nested prior frame on `Fin 2` with `E_0 = E_1 = {1}` (not
  factive at `0`) whose prior fails Simple Trust and Total Trust.
-/

namespace Cleanroom.Lit.LitDdbFacts.AuditR3

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbFacts
  Cleanroom.Lit.LitDdbFacts.ExamplesPrior

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Every row of a prior frame is a candidate of its (regular) prior.
Source: none: audit r3 probe Q1
Kind: L
Fidelity: n/a -/
theorem priorFrame_row_mem_cands (Q : PriorFrame W) (w : W) :
    Q.row w ∈ Q.toFrame.cands Q.μ :=
  Frame.mem_cands.2 ⟨w, Q.μ_pos w, rfl⟩

/-- A row is positive on its evidence.
Source: none: audit r3 probe Q1
Kind: L
Fidelity: n/a -/
theorem priorFrame_row_pos_of_mem (Q : PriorFrame W) {w v : W} (hv : v ∈ Q.Ev w) :
    0 < Q.row w v := by
  unfold PriorFrame.row
  rw [if_pos hv]
  exact div_pos (Q.μ_pos v) (Q.mass_Ev_pos w)

/-- If a distribution `ρ` gives mass `1` to a set `q`, every world where `ρ` is positive lies in
`q`.
Source: none: audit r3 probe Q1
Kind: L
Fidelity: n/a -/
theorem mem_of_mass_eq_one {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {q : Finset W}
    (hq : mass ρ q = 1) {x : W} (hx : 0 < ρ x) : x ∈ q := by
  by_contra hxq
  have hsub : q ⊆ univ.erase x := fun u hu =>
    mem_erase.2 ⟨fun h => hxq (h ▸ hu), mem_univ _⟩
  have hle := mass_mono hρ.1 hsub
  have hsplit : mass ρ (univ.erase x) + ρ x = 1 := by
    rw [mass, Finset.sum_erase_add _ _ (mem_univ x)]
    exact hρ.2
  linarith

/-- **Q1. Total Trust of the prior forces transitive evidence on any prior frame**:
`v ∈ E_w → E_v ⊆ E_w`. No nestedness is assumed.
Source: none: audit r3 probe Q1 (report E1's converse question, first half)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond Total Trust of the prior -/
theorem priorFrame_Ev_subset_of_mem_of_totalTrust (Q : PriorFrame W)
    (h : TotalTrust Q.μ Q.toFrame) {v w : W} (hv : v ∈ Q.Ev w) : Q.Ev v ⊆ Q.Ev w := by
  have hrow : TotalTrust (Q.row w) Q.toFrame :=
    totalTrust_cands Q.μ_mem h _ (priorFrame_row_mem_cands Q w)
  have hpa : PositiveAccess Q.toFrame (Q.row w) :=
    positiveAccess_of_simpleTrust (Q.row_mem w) hrow.simpleTrust
  have h1 := hpa (Q.Ev w) (Q.mass_row_Ev w)
  have hvA := mem_of_mass_eq_one (Q.row_mem w) h1 (priorFrame_row_pos_of_mem Q hv)
  rw [mem_filter] at hvA
  have h2 : mass (Q.row v) (Q.Ev w) = 1 := hvA.2
  intro x hx
  exact mem_of_mass_eq_one (Q.row_mem v) h2 (priorFrame_row_pos_of_mem Q hx)

/-- Q1 collected with the package's own factivity: Total Trust of the prior makes the evidence
factive and transitive (the two structural hypotheses of
`PriorFrame.totalTrust_of_factive_of_trans_of_nested`), on any prior frame.
Source: none: audit r3 probe Q1
Kind: C
Fidelity: n/a -/
theorem priorFrame_factive_trans_of_totalTrust (Q : PriorFrame W)
    (h : TotalTrust Q.μ Q.toFrame) :
    (∀ w, w ∈ Q.Ev w) ∧ ∀ v w, v ∈ Q.Ev w → Q.Ev v ⊆ Q.Ev w :=
  ⟨Q.mem_Ev_self_of_simpleTrust h.simpleTrust, fun _ _ hv => priorFrame_Ev_subset_of_mem_of_totalTrust Q h hv⟩

/-! ## Q2: nestedness alone gives nothing -/

/-- The uniform prior on two worlds.
Source: none: audit r3 probe Q2
Kind: D
Fidelity: n/a -/
def bad2μ : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Regular.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bad2μ_pos : ∀ w, 0 < bad2μ w := by
  intro w; fin_cases w <;> norm_num [bad2μ]

/-- Sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bad2μ_sum : ∑ w, bad2μ w = 1 := by
  norm_num [Fin.sum_univ_two, bad2μ]

/-- Evidence `E_0 = E_1 = {1}`: nested (the two sets coincide) but not factive at `0`.
Source: none: audit r3 probe Q2
Kind: D
Fidelity: n/a -/
def bad2Ev : Fin 2 → Finset (Fin 2) := ![{1}, {1}]

/-- Nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bad2Ev_nonempty : ∀ w, (bad2Ev w).Nonempty := by
  intro w; fin_cases w <;> simp [bad2Ev]

/-- The nested, non-factive prior frame.
Source: none: audit r3 probe Q2
Kind: D
Fidelity: n/a -/
def bad2Q : PriorFrame (Fin 2) := ⟨bad2μ, bad2μ_pos, bad2μ_sum, bad2Ev, bad2Ev_nonempty⟩

/-- It is nested.
Source: none: audit r3 probe Q2
Kind: L
Fidelity: n/a -/
theorem bad2Q_nested : bad2Q.Nested := by
  intro v w _
  fin_cases v <;> fin_cases w <;> decide

/-- It is not factive at world `0`.
Source: none: audit r3 probe Q2
Kind: L
Fidelity: n/a -/
theorem bad2Q_not_factive : (0 : Fin 2) ∉ bad2Q.Ev 0 := by decide

/-- **Q2.** Its prior fails Simple Trust (factivity is forced by Simple Trust, F14), hence
Total Trust: nestedness does not by itself make the prior trust the frame, so the antecedent of
`totalTrust_of_nested_of_simpleTrust` is a real hypothesis.
Source: none: audit r3 probe Q2
Kind: N+
Fidelity: n/a -/
theorem bad2Q_summary :
    bad2Q.Nested ∧ ¬ SimpleTrust bad2Q.μ bad2Q.toFrame ∧ ¬ TotalTrust bad2Q.μ bad2Q.toFrame := by
  have hns : ¬ SimpleTrust bad2Q.μ bad2Q.toFrame := fun h =>
    bad2Q_not_factive (bad2Q.mem_Ev_self_of_simpleTrust h 0)
  exact ⟨bad2Q_nested, hns, fun h => hns h.simpleTrust⟩

end

end Cleanroom.Lit.LitDdbFacts.AuditR3
