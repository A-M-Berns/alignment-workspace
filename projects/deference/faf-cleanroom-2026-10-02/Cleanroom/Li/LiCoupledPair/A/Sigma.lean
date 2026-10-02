import Cleanroom.Li.LiCoupledPair.DefsHeavy
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Construction.LUV.Endpoints

/-!
# `li-coupled-pair` · A/Sigma: the quote package discharged by Σ₁-completeness (T1.1, T1.4)

**T1.1.** For *any* market `H` with an exact market program `MH : MarketComputation H`, any e.c.
LUV family `XH` of `H`'s language and any deferral function `f`, the sequence
`n ↦ 𝔼^H_{f n}(XH n)` is a total computable `[0,1]`-rational sequence (FAF's
`MarketComputation.expectQuoteAt` with `expectQuoteAt_computable`), so FAF's
`RationalQuoteCode.ofComputable T` names it by a quotation code whose threshold LUV
`sigmaQuoteCode.luv n = ⌜𝔼^H_{f n}(XH n)⌝` every completed-theory world of `paperDP T` values at
`H`'s realized expectation (`RationalQuoteCode.reflected` at `paperQuotationPresentation T`,
`expectQuoteAt_cast`). Hence `CrossQuotePackage H (paperDP T) f XH (sigmaQuoteCode …).luv`
holds with **no hypothesis** beyond `XH`'s e.c. certificate and `[T.Δ₁] [𝗥₀ ⪯ T]`:
`crossQuotePackage_sigma`. This is the sources' intended discharge — "`Γ_A` extends PA and proves
the outputs of the coupled construction, so each forecast-target LUV is determined via `Γ_A`"
([[fa-positive-results-corrected-v3]] (A3)); "`Γ` determines the coupled computation" is ordinary
Σ₁-completeness through a decidable enumeration (anson-2-014) — and it is the composition of
`li-quote-lane`'s same-market instance `crossQuotePackage_paper_self` with `paperMarketComputation T`
replaced by an arbitrary `MH` (two distinct markets).

**What it costs, and what it does not give (mandate T1 traps).** (i) It is **not** a ledger: `A`'s
process is `paperDP T` itself, nothing is adjoined; the `reflected` field is a theorem about
`T`'s Σ₁-completeness, so the package counts **zero** `(c)` clauses. (ii) `reflected` is vacuous
over an inconsistent `DPA`: the witness ships `hworldA := paperDP_hworld T`
(`[𝗣𝗔⁻ ⪯ T] [Consistent T]`) beside it, as every FAF consumer does. (iii) **Timing: none.**
`paperDP T` decides the literal `(sigmaQuoteCode.luv n).gt r` at a dovetail stage nobody controls
(`bli-found` F-14); the determinacy is via the *completed* theory. A dependent needing "decided by
stage `σ(n)`" takes the mirror ledger (`li-quote-lane` T2.4), not this. Fidelity against (A3):
`exact (determinacy); timing: none`. (iv) Σ₁-completeness is carried by `[𝗥₀ ⪯ T]` through
`BooleanQuoteCode.ofComputable`; no `RepresentsComputations` instance is added.

**Scope: one-way in timing, two-way in determinacy** (`H` reads `A` at controlled stages in the
witness, `A`'s theory determines `H`'s expectations at no stage).

**Consumer rows.** `.determinedViaTheory`, `.worldValued`, `.approxDetermined_mesh` are
`li-quote-lane`'s `CrossQuote.lean` at the discharged package (cited, not re-proved; `L`); one
worked instance of FAF's endpoint `lic_expect_combination_provind_ge_ofDetermined` at the package
(`sigma_expect_provind_ge`, `L`) shows the discharge feeds FAF's expectation provability
induction; the T1.4 bridges are `sigma_determinedViaTheory_affineImage` (the `LUVCombination`
affine-image predicate) and `sigma_approxDetermined_mesh` (the `AffineCombination` approximate
predicate), through `li-asymp-calc`.
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## The sequence `A` names: `H`'s exact realized deferred expectation -/

section value

variable {H : History} (MH : MarketComputation H) (XH : ℕ → LUV) (f : DeferralFunction)

/-- `H`'s exact rational day-`f n` expectation of `XH n`, through `H`'s market program
(FAF's `MarketComputation.expectQuoteAt`): the sequence `A`'s quotation code names. One index
(the day), as `RationalQuoteCode` wants. Scope: one-way in timing.
Source: [[faithful-acceleration]] §4(II) (root-fa-002: the LUV `⌜𝔼^H_{f(n)}(X)⌝`); [[fa-positive-results-corrected-v3]] (A2)
Kind: D
Fidelity: exact (FAF's `expectQuoteAt`)
Hyps: n/a -/
noncomputable def sigmaValue (n : ℕ) : ℚ := MH.expectQuoteAt XH n (f.f n)

/-- The sequence is computable from `XH`'s e.c. certificate and the deferral function's
computability (FAF's `expectQuoteAt_computable`).
Source: mandate T1.1; FAF `MarketComputation.expectQuoteAt_computable`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigmaValue_computable (hX : LUV.MachineThresholdCodeSeq XH) :
    Computable (sigmaValue MH XH f) :=
  ((MH.expectQuoteAt_computable hX).comp (Computable.id.pair f.computable)).of_eq fun _ => rfl

/-- The sequence lies in `[0,1]` (FAF's `expectQuoteAt_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigmaValue_mem (n : ℕ) : 0 ≤ sigmaValue MH XH f n ∧ sigmaValue MH XH f n ≤ 1 :=
  MH.expectQuoteAt_mem_Icc XH n (f.f n)

/-- The sequence *is* `H`'s real-valued realized expectation (FAF's `expectQuoteAt_cast`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigmaValue_cast (n : ℕ) : (XH n).expect H (f.f n) = (sigmaValue MH XH f n : ℝ) :=
  MH.expectQuoteAt_cast XH n (f.f n)

end value

/-! ## T1.1: the discharge -/

section sigma

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
variable {H : History} (MH : MarketComputation H) (XH : ℕ → LUV)
  (hX : LUV.MachineThresholdCodeSeq XH) (f : DeferralFunction)

/-- **`A`'s quotation code for `H`'s realized deferred expectations**: FAF's `RationalQuoteCode T`
naming `sigmaValue MH XH f` (`RationalQuoteCode.ofComputable`), whose threshold LUV
`sigmaQuoteCode.luv n` is `⌜𝔼^H_{f n}(XH n)⌝` of `A`'s language — a tag-`2` quotation atom family,
e.c. (`.poly`), with no fresh atom. Scope: one-way in timing, two-way in determinacy.
Source: [[faithful-acceleration]] §4(II) (root-fa-002); [[fa-positive-results-corrected-v3]] (A2) ("fixed template plus numeral"); FAF `RationalQuoteCode.ofComputable`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sigmaQuoteCode : RationalQuoteCode T (sigmaValue MH XH f) :=
  RationalQuoteCode.ofComputable T (sigmaValue_computable MH XH f hX) (sigmaValue_mem MH XH f)

/-- **T1.1 (headline). The cross-market quote package is discharged over `paperDP T`:** for any
market `H` with an exact market program `MH`, any e.c. LUV family `XH` and any deferral function
`f`, `CrossQuotePackage H (paperDP T) f XH (sigmaQuoteCode T MH XH hX f).luv` holds — `quote_codes`
is FAF's `.poly`, `reflected` is FAF's `RationalQuoteCode.reflected` at
`paperQuotationPresentation T` rewritten by `expectQuoteAt_cast`. **No hypothesis** beyond `XH`'s
e.c. certificate and `[T.Δ₁] [𝗥₀ ⪯ T]`; zero `(c)` clauses; two distinct markets (`H` arbitrary,
`A = liaHistory (paperDP T)` through the witness). Composition of FAF's Σ₁-completeness
(`BooleanQuoteCode.ofComputable`, inside `ofComputable`) with `H`'s computability
(`expectQuoteAt_computable`). **Timing: none** — determinacy via the completed theory, at no
controlled stage (module docstring, trap (iii)); **carries no world** — pair it with
`paperDP_hworld T` (`sigmaPair_paper`'s `hworldA`). Scope: one-way in timing, two-way in
determinacy.
Source: [[faithful-acceleration]] §4(II) (root-fa-002); [[fa-positive-results-corrected-v3]] (A3) ("determined via `Γ_A` … no bound on how long the construction takes to run"); anson-2-014 ("ordinary Σ₁-completeness, no Löb issue"); [[route-sparse-schedule]] §10 (S1) (vq-wiki-029)
Kind: C
Fidelity: exact (determinacy); timing: none
Hyps: (a) none -/
theorem crossQuotePackage_sigma :
    CrossQuotePackage H (paperDP T) f XH (sigmaQuoteCode T MH XH hX f).luv := by
  refine ⟨(sigmaQuoteCode T MH XH hX f).poly, fun n v hv => ?_⟩
  rw [sigmaValue_cast MH XH f n]
  exact (sigmaQuoteCode T MH XH hX f).reflected (paperQuotationPresentation T) n v hv

/-! ## Consumer rows, at the discharged package (cited from `li-quote-lane`'s `CrossQuote.lean`) -/

/-- At the discharged package, `LUVCombination.DeterminedViaTheory` of the quote family at `H`'s
realized expectations, for any market `A` (`li-quote-lane` `CrossQuotePackage.determinedViaTheory`):
the `hdet0` input of FAF's `lic_expect_combination_provind_*_ofDetermined`. The (c) that
`CrossQuote.lean` lists for this row is discharged here: there is no hypothesis.
Source: mandate T1.1 (consumer rows); `li-quote-lane` T2.2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigma_determinedViaTheory (A : History) :
    LUVCombination.DeterminedViaTheory
      (fun n => LUVCombination.ofLUV ((sigmaQuoteCode T MH XH hX f).luv n)) A (paperDP T)
      (fun n => (XH n).expect H (f.f n)) :=
  (crossQuotePackage_sigma T MH XH hX f).determinedViaTheory A

/-- At the discharged package, `LUVCombination.WorldValued` of the quote family in `paperDP T`
(`li-quote-lane` `CrossQuotePackage.worldValued`): the `hwv` input of the endpoints.
Source: mandate T1.1 (consumer rows); `li-quote-lane` T2.2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigma_worldValued :
    LUVCombination.WorldValued
      (fun n => LUVCombination.ofLUV ((sigmaQuoteCode T MH XH hX f).luv n)) (paperDP T) :=
  (crossQuotePackage_sigma T MH XH hX f).worldValued

/-- **T1.4, the `AffineCombination` approximate form:** at the discharged package, the
precision-`(n+1)` mesh of the quote family is `AffineCombination.ApproxDeterminedViaTheory` at
`H`'s realized expectations with error `1/(n+1)` (`li-quote-lane`
`CrossQuotePackage.approxDetermined_mesh`, through `li-asymp-calc`'s
`DeterminedVia.approxDetermined_mesh_ofLUV`): the input of FAF's `lic_wubaff` /
`affine_provind_theory_*`.
Source: mandate T1.4 (plan: "both the `LUVCombination` and the `AffineCombination` predicate")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigma_approxDetermined_mesh (A : History) :
    AffineCombination.ApproxDeterminedViaTheory
      (fun n => (LUVCombination.ofLUV ((sigmaQuoteCode T MH XH hX f).luv n)).meshAffine (n + 1))
      A (paperDP T) (fun n => (XH n).expect H (f.f n)) (fun n => 1 / ((n : ℝ) + 1)) :=
  (crossQuotePackage_sigma T MH XH hX f).approxDetermined_mesh A

/-- **T1.4, the `LUVCombination` affine-image form:** at the discharged package, the affine images
`α · ⌜𝔼^H_{f n}(XH n)⌝ + β` are `LUVCombination.DeterminedViaTheory` at `α · 𝔼^H_{f n}(XH n) + β`
(`li-asymp-calc`'s `DeterminedVia.determinedViaTheory_affineImage`).
Source: mandate T1.4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigma_determinedViaTheory_affineImage (α β : ℚ) (A : History) :
    LUVCombination.DeterminedViaTheory
      (fun n => LUVCombination.affineImage α β ((sigmaQuoteCode T MH XH hX f).luv n)) A (paperDP T)
      (fun n => α * (XH n).expect H (f.f n) + β) :=
  DeterminedVia.determinedViaTheory_affineImage α β A
    (crossQuotePackage_sigma T MH XH hX f).reflected

/-- **One worked endpoint instance (`L`): the discharge feeds FAF's expectation provability
induction.** With `A := liaHistory (paperDP T)` (FAF's `paperLIA` instance), the package's
`.boundedSequence`, `.worldValued` and `.determinedViaTheory` are exactly the inputs of
`lic_expect_combination_provind_ge_ofDetermined`: if `H`'s realized deferred expectations are all
`≥ c`, then `A`'s day-`n` expectations of the quote LUVs `⌜𝔼^H_{f n}(XH n)⌝` are asymptotically
`≥ c`. `hworld` is `paperDP_hworld T` (`[𝗣𝗔⁻ ⪯ T] [Consistent T]`). Plumbing: the content is
FAF's theorem; this row shows the discharged package is the right shape for it.
Source: mandate T1.1 (consumer rows); FAF `lic_expect_combination_provind_ge_ofDetermined` (`Construction/LUV/Endpoints.lean`)
Kind: L
Fidelity: exact
Hyps: (a) none (`hc` is the instance's own antecedent) -/
theorem sigma_expect_provind_ge [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T] (c : ℝ)
    (hc : ∀ n, c ≤ (XH n).expect H (f.f n)) :
    (fun n => ((sigmaQuoteCode T MH XH hX f).luv n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => c) := by
  haveI := paperLIA T
  have h := lic_expect_combination_provind_ge_ofDetermined
    ((crossQuotePackage_sigma T MH XH hX f).boundedSequence (liaHistory (paperDP T)))
    (sigma_worldValued T MH XH hX f) (sigma_determinedViaTheory T MH XH hX f (liaHistory (paperDP T)))
    c hc (paperDP_hworld T)
  simpa only [ofLUV_expect] using h

end sigma

end Cleanroom.Li.LiCoupledPair.A
