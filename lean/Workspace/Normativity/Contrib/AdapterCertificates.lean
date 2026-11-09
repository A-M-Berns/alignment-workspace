/-
# The adapter's certificates exist where the region excludes or marks

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, follow-up of 2026-11-09,
matter 5.

`WarrantInductor.Problem` carries, for each response, a cited functional certificate bounding
its score from above (`upper`) and one bounding its negation (`lower`); `Problem.Excludes` and
`Problem.Margins` say those certificates cite live rows and certify the threshold.  From
`IncompatibilitySemantics.certEntails_iff_sem`: every valid upper bound on a rational functional
over a bundle's region has a cited functional certificate of at most that value
(`exists_citedFunctional`).  So where every inadequate response scores at most a rational
`t ≤ τ` on the region, certificates making `Excludes` hold exist (`excludes_of_region`); and
where every margin witness scores at least a rational `t ≥ τ + δ` on the region, certificates
making `Margins` hold at tolerance `0` exist (`margins_of_region`).

Not derived: the case of a threshold with no rational between it and the region's supremum
(that needs the supremum of a rational functional over a rational polytope to be rational and
attained, which is not proved here), and `Margins` at a positive tolerance (the tolerance is
multiplied by the certificate's mass, which validity on the region does not bound; the
corresponding semantic condition is the margin on the region with every row relaxed by the
tolerance).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.IncompatibilitySemantics
import Workspace.Normativity.Contrib.WarrantInductor

namespace Workspace.Normativity.Contrib.AdapterCertificates

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.RowAlternative
open Workspace.Normativity.Contrib.IncompatibilitySemantics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantForce
open Workspace.Normativity.Contrib.WarrantInductor
open Finset

variable {d : ℕ}

/-- **A valid upper bound on a functional over a bundle's region has a cited certificate**: a
functional certificate whose positively weighted rows are admitted into the bundle under their
citations and whose value is at most the bound. -/
theorem exists_citedFunctional (B : Bundle (Cite d) d) (ℓ : Fin d → ℚ) (v : ℚ)
    (h : ∀ y, B.Region y → ∑ j, ℓ j * y j ≤ v) :
    ∃ c : CitedFunctional d ℓ, c.CitesLive B ∧ c.cert.value ≤ v := by
  have hsem : SemEntails (B.map CitedRow.row) ⟨ℓ, v⟩ := fun x hcube hx =>
    h x ((region_iff_satAll B x).2
      ((satAll_append _ _ _).2 ⟨hx, (cubeRows_sat_iff x).2 hcube⟩))
  obtain ⟨m, cert, hall⟩ := (certEntails_iff_sem _ _).2 hsem
  have hcite : ∀ i, ∃ q : Cite d, VerdictCert.RowAdmitted B q (cert.row i) := by
    intro i
    rcases hall i with hmem | hu | hl
    · obtain ⟨c, hc, hrow⟩ := List.mem_map.1 hmem
      exact ⟨c.cites, Or.inl (hrow ▸ hc)⟩
    · exact ⟨Cite.sub 0, Or.inr (Or.inl hu)⟩
    · exact ⟨Cite.sub 0, Or.inr (Or.inr hl)⟩
  choose cites hcites using hcite
  exact ⟨⟨m, ⟨cert.mult, cert.row, cert.mult_nonneg, cert.coeff_sum⟩, cites⟩,
    fun i _ => hcites i, cert.const_le⟩

/-- The hypothesis of `exists_citedFunctional` inhabited: on `SeedStatics.widenSeed` the bound
`−P(0) ≤ −1/2` has a cited certificate. -/
theorem citedFunctional_witness :
    ∃ c : CitedFunctional 1 (fun _ => -1),
      c.CitesLive (forcedBundle widenSeed [] DocketState.quiet (Settlement.empty 1)) ∧
        c.cert.value ≤ -1/2 :=
  exists_citedFunctional _ _ _ fun y hy => by
    have := defeat_widens.1 y hy
    simp only [Fin.sum_univ_one]
    linarith

variable {Q : Type} [Fintype Q] [DecidableEq Q]

open Classical in
/-- **Exclusion certificates exist where the region excludes**: if every inadequate response
scores at most a rational `t ≤ τ` at every point of the bundle's region, the problem with
suitable `upper` certificates satisfies `Excludes` on the bundle. -/
theorem excludes_of_region (P : Problem d Q) (B : Bundle (Cite d) d) (t : ℚ)
    (ht : (t : ℝ) ≤ P.τ)
    (h : ∀ q ∉ P.A, ∀ y, B.Region y → P.offset q + ∑ j, P.ℓ q j * y j ≤ t) :
    ∃ upper : (q : Q) → CitedFunctional d (P.ℓ q),
      ({ P with upper := upper } : Problem d Q).Excludes B := by
  have hex : ∀ q, q ∉ P.A →
      ∃ c : CitedFunctional d (P.ℓ q), c.CitesLive B ∧ c.cert.value ≤ t - P.offset q :=
    fun q hq => exists_citedFunctional B (P.ℓ q) (t - P.offset q) fun y hy => by
      have := h q hq y hy
      linarith
  obtain ⟨upper, hupper⟩ : ∃ upper : (q : Q) → CitedFunctional d (P.ℓ q),
      ∀ q (hq : q ∉ P.A), upper q = (hex q hq).choose :=
    ⟨fun q => if hq : q ∈ P.A then P.upper q else (hex q hq).choose, fun q hq => dif_neg hq⟩
  refine ⟨upper, fun q hq => ?_⟩
  show (upper q).CitesLive B ∧ ((P.offset q + (upper q).cert.value : ℚ) : ℝ) ≤ P.τ
  rw [hupper q hq]
  obtain ⟨hlive, hval⟩ := (hex q hq).choose_spec
  refine ⟨hlive, le_trans ?_ ht⟩
  exact_mod_cast (by linarith : P.offset q + (hex q hq).choose.cert.value ≤ t)

open Classical in
/-- **Margin certificates exist where the region marks**, at tolerance `0`: if every margin
witness scores at least a rational `t ≥ τ + δ` at every point of the bundle's region, the
problem with suitable `lower` certificates satisfies `Margins` on the bundle at tolerance `0`. -/
theorem margins_of_region (P : Problem d Q) (B : Bundle (Cite d) d) (t : ℚ)
    (ht : P.τ + P.δ ≤ (t : ℝ))
    (h : ∀ q ∈ P.A₁, ∀ y, B.Region y → t ≤ P.offset q + ∑ j, P.ℓ q j * y j) :
    ∃ lower : (q : Q) → CitedFunctional d (fun j => -(P.ℓ q j)),
      ({ P with lower := lower } : Problem d Q).Margins B 0 := by
  have hex : ∀ q, q ∈ P.A₁ →
      ∃ c : CitedFunctional d (fun j => -(P.ℓ q j)),
        c.CitesLive B ∧ c.cert.value ≤ P.offset q - t :=
    fun q hq => exists_citedFunctional B (fun j => -(P.ℓ q j)) (P.offset q - t) fun y hy => by
      have := h q hq y hy
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
  obtain ⟨lower, hlower⟩ : ∃ lower : (q : Q) → CitedFunctional d (fun j => -(P.ℓ q j)),
      ∀ q (hq : q ∈ P.A₁), lower q = (hex q hq).choose :=
    ⟨fun q => if hq : q ∈ P.A₁ then (hex q hq).choose else P.lower q, fun q hq => dif_pos hq⟩
  refine ⟨lower, fun q hq => ?_⟩
  show (lower q).CitesLive B ∧
    P.τ + P.δ ≤ ((P.offset q - (lower q).cert.value - (lower q).cert.mass * 0 : ℚ) : ℝ)
  rw [hlower q hq]
  obtain ⟨hlive, hval⟩ := (hex q hq).choose_spec
  refine ⟨hlive, le_trans ht ?_⟩
  exact_mod_cast (by linarith :
    t ≤ P.offset q - (hex q hq).choose.cert.value - (hex q hq).choose.cert.mass * 0)

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.AdapterCertificates.exists_citedFunctional
#print axioms Workspace.Normativity.Contrib.AdapterCertificates.citedFunctional_witness
#print axioms Workspace.Normativity.Contrib.AdapterCertificates.excludes_of_region
#print axioms Workspace.Normativity.Contrib.AdapterCertificates.margins_of_region

end Workspace.Normativity.Contrib.AdapterCertificates
