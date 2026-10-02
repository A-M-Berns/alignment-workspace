import Cleanroom.Trust.TrustMerge.Defs
import LogicalInduction.Construction.Freeze.Oracle

/-!
# `trust-merge` · Treacherous: priced out, but on no fixed day (T7, 017)

**trust-lab-017 / [[merging-inductors-ideate]] Idea 6.** "A trader inside `A` that waits for `H`
to trust `A` and then defects loses budget and is eventually priced out (LI learning), but the
criterion gives no bound on *when*."

(i) **"Priced out" is the criterion itself** (`treacherous_priced_out`): for the mirror inductor
`A` (or any inductor), no `EfficientlyComputable` trader exploits it — `IsLogicalInductor`'s
`noExploit` field, verbatim (Kind L). Nothing more is claimed: "its effect on `B` washes out" is
not a theorem of this package, and the one-big-lie shadow (`OneBigLie.lean`) is why.

(ii) **"Timing unbounded" as a theorem** (`timing_unbounded`, Kind C, (a)): FAF's corrected
`thm:ifp` (`FreezeOracle.lic_iff_of_finiteSupport`: a *finite-support* perturbation of a
computable market preserves inductor-hood, with no condition on the moved sentences) applied to
the one-coordinate patch `patchPrice A T ψ v` — `A` with its day-`T` price of `ψ` overwritten by
`v ∈ [0,1]`. So for every inductor `A`, every day `T`, every sentence `ψ` and every rational `[0,1]`-value
`v` there is an inductor over the same process agreeing with `A` off `(T, ψ)` whose day-`T` price
of `ψ` is `v`: **every asymptotic guarantee of this package is silent about any fixed day.** The
"every value" form promised by the mandate is reached (the patch is one coordinate, so finite
support holds outright); what the paper's finite-*days* statement would have given is not needed
and, per FAF, is false. Computability of the patched market is the only work
(`patchPrice_computableMarket`): the patched quote table is a Boolean `cond` on the paired index.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction

/-- **(i) Priced out is the criterion:** no efficiently computable trader exploits an inductor —
in particular no treacherous trader inside the mirror inductor `A`.
Source: trust-lab-017 ("eventually priced out (LI learning)"); [[merging-inductors-ideate]] Idea 6
("Candidate Proposition 6 … is just the LI criterion applied to `A`")
Kind: L
Fidelity: exact (the `IsLogicalInductor` field)
Hyps: (a) none -/
theorem treacherous_priced_out {A : History} {DPA : DeductiveProcess}
    [hLI : IsLogicalInductor A DPA] (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits A DPA :=
  hLI.noExploit Tr hTr

/-- **The one-coordinate patch**: `A` with its day-`T` price of `ψ` replaced by `v`.
Source: trust-lab-017 (the treacherous turn at one day); FAF `thm:ifp` (finite-support
perturbations)
Kind: D
Fidelity: exact -/
noncomputable def patchPrice (A : History) (T : ℕ) (ψ : Sentence) (v : ℚ) : History :=
  fun d φ => if d = T ∧ φ = ψ then (v : ℝ) else A d φ

/-- The patch differs from `A` on one coordinate only (FAF's `FiniteSupportPerturbation`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem patchPrice_finiteSupport (A : History) (T : ℕ) (ψ : Sentence) (v : ℚ) :
    FiniteSupportPerturbation A (patchPrice A T ψ v) := by
  refine ⟨{(T, ψ)}, fun d φ h => ?_⟩
  unfold patchPrice
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact h (Finset.mem_singleton_self _)

/-- **The patched market is computable**: its quote table is `A`'s with one entry overwritten,
a Boolean `cond` on the paired index.
Source: none: infrastructure (FAF `ComputableMarket.ofComputableTable`)
Kind: L
Fidelity: n/a -/
theorem patchPrice_computableMarket {A : History} (M : MarketComputation A) (T : ℕ)
    (ψ : Sentence) (v : ℚ) (hv : 0 ≤ v ∧ v ≤ 1) :
    ComputableMarket (patchPrice A T ψ v) := by
  classical
  refine ComputableMarket.ofComputableTable
    (fun n c => if n = T ∧ c = Encodable.encode ψ then v else M.quote n c) ?_ ?_ ?_
  · intro n φ
    unfold patchPrice
    split_ifs
    · exact ⟨by exact_mod_cast hv.1, by exact_mod_cast hv.2⟩
    · exact M.price_mem_Icc n φ
  · intro n φ
    unfold patchPrice
    by_cases h : n = T ∧ φ = ψ
    · rw [if_pos h, if_pos ⟨h.1, by rw [h.2]⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, Encodable.encode_injective h'.2⟩),
        M.quote_exact]
  · have heval : Partrec fun z : ℕ => M.code.eval z :=
      Nat.Partrec.Code.eval_part.comp (Computable.const M.code) Computable.id
    have henc : Computable fun z : ℕ => Encodable.encode (M.quote z.unpair.1 z.unpair.2) :=
      heval.of_eq fun z => Part.eq_some_iff.mpr (M.code_spec z)
    have hq : Computable fun z : ℕ => M.quote z.unpair.1 z.unpair.2 :=
      Computable.encode_iff.mp henc
    have hc : Computable fun z : ℕ => decide (z = Nat.pair T (Encodable.encode ψ)) := by
      obtain ⟨_, hpr⟩ :=
        (Primrec.eq.comp Primrec.id (Primrec.const (Nat.pair T (Encodable.encode ψ))))
      exact hpr.to_comp.of_eq (fun z => decide_eq_decide.mpr Iff.rfl)
    have hcond := Computable.cond hc (Computable.const v) hq
    refine Computable.encode.comp (hcond.of_eq fun z => ?_)
    by_cases h : z = Nat.pair T (Encodable.encode ψ)
    · subst h
      simp
    · have h' : ¬ (z.unpair.1 = T ∧ z.unpair.2 = Encodable.encode ψ) := by
        rintro ⟨h1, h2⟩
        apply h
        rw [← Nat.pair_unpair z, h1, h2]
      simp [h, h']

/-- **(ii) Timing unbounded (headline).** For every inductor `A` over `DPA`, every day `T`,
every sentence `ψ` and every rational `[0,1]`-value `v`, the one-coordinate patch is an inductor over the
same process, agrees with `A` off `(T, ψ)`, and prices `ψ` at `v` on day `T`. Every asymptotic
guarantee of this package is therefore silent about any fixed day: the treacherous turn can
happen on the day of one's choosing, at the price of one's choosing. FAF's corrected `thm:ifp`
(`FreezeOracle.lic_iff_of_finiteSupport`) at a one-coordinate `FiniteSupportPerturbation`; both
markets computable (`patchPrice_computableMarket`).
Source: trust-lab-017 ("the criterion gives no bound on *when*"); mandate T7 (017 (ii)); FAF
`thm:ifp` (finite-support form)
Kind: C
Fidelity: exact (the "every value" form; FAF's finite-support hypothesis is met outright)
Hyps: (a) none -/
theorem timing_unbounded {A : History} {DPA : DeductiveProcess} [hLI : IsLogicalInductor A DPA]
    (T : ℕ) (ψ : Sentence) (v : ℚ) (hv : 0 ≤ v ∧ v ≤ 1) :
    IsLogicalInductor (patchPrice A T ψ v) DPA ∧ patchPrice A T ψ v T ψ = (v : ℝ) ∧
      ∀ d φ, ¬ (d = T ∧ φ = ψ) → patchPrice A T ψ v d φ = A d φ := by
  obtain ⟨M⟩ := hLI.marketComputable.nonemptyComputation
  refine ⟨(FreezeOracle.lic_iff_of_finiteSupport A _ DPA hLI.marketComputable
    (patchPrice_computableMarket M T ψ v hv) (patchPrice_finiteSupport A T ψ v)).mp hLI,
    by simp [patchPrice], fun d φ h => by simp [patchPrice, h]⟩

/-- **Every value on every day**: the existential form of `timing_unbounded`.
Source: trust-lab-017; mandate T7 ("for every day `T` and every `[0,1]` value `v` there is an
inductor `A'` over `DPA` agreeing with `A` off day `T` whose day-`T` price of the quote is `v`")
Kind: L
Fidelity: exact (stronger than the mandate's: agreeing off one coordinate, not off one day)
Hyps: (a) none -/
theorem exists_inductor_any_price {A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] (T : ℕ) (ψ : Sentence) (v : ℚ) (hv : 0 ≤ v ∧ v ≤ 1) :
    ∃ A' : History, IsLogicalInductor A' DPA ∧ A' T ψ = (v : ℝ) ∧
      ∀ d φ, ¬ (d = T ∧ φ = ψ) → A' d φ = A d φ :=
  ⟨patchPrice A T ψ v, timing_unbounded T ψ v hv⟩

end Cleanroom.Trust.TrustMerge
