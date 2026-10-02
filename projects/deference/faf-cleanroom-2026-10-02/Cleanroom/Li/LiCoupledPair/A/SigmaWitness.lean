import Cleanroom.Li.LiCoupledPair.A.Sigma
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.PaperQuotation

/-!
# `li-coupled-pair` · A/SigmaWitness: the quote names a machine (T1.2) and the Σ₁ pair over the
paper process (T1.3, N+; T1.4 instantiated)

**T1.2 (plan rigor critique 17).** For `H := liaHistory DPH` with `DPH` computable, FAF's named
market program `liaMarketComputation DPH hH` (the `MarketComputation` that `LIA_is_logical_inductor`
supplies) computes `H` exactly: `H n φ = (MH.quote n ⌜φ⌝ : ℝ)` (`liaHistory_eq_machine`,
`MH.quote_exact`) and `𝔼^H_m(X n) = (MH.expectQuoteAt X n m : ℝ)` (`liaHistory_expect_eq_machine`,
`expectQuoteAt_cast`). So the quotation LUV `⌜𝔼^H_{f n}(XH n)⌝` of `A/Sigma.lean` names a
*machine* (the program `MH.code`), and `H` is what that machine computes — the identification the
sources take for granted ("the fixed index of the program computing `H`'s market",
[[route-negative-introspective]] §4.3).

**T1.3 (N+).** `sigmaPair_paper : SigmaPair` at `T := 𝗜𝚺₁`: `A := liaHistory (paperDP 𝗜𝚺₁)` is the
bare paper LIA; `H` is `li-quote-lane`'s one-way reader `paperOneWayPair.H` — FAF's LIA over
`paperDP 𝗜𝚺₁ ⊕ (ledger of A's day-n prices of the atoms ⟨0, ⟨j, n⟩⟩, next-day publication)`;
`XH := cleanX` (indicators of the tag-`0` atoms `⟨0, ⟨0, n⟩⟩`), `f := succDeferral`. N+ grounds
*proved*: the two processes differ (`sigmaPair_paper_processes_differ`: an affirmed ledger literal
sits in a stage of `H`'s process and in no stage of `paperDP 𝗜𝚺₁`, by `paperDP_cleanroomFree`);
`XH` is outside the ledger family (`cleanX_tagFree`: no threshold sentence of any `cleanX n`
mentions a family-`3` atom); both polarities occur in `H`'s ledger
(`sigmaPair_paper_both_polarities`). As in `li-quote-lane` F7, **no claim that the quote values
vary** is made — that would evaluate the LIA. Scope: one-way in timing, two-way in determinacy.
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## T1.2: the quote names a machine; `H` is what it computes -/

/-- **T1.2.** FAF's LIA over a computable process is computed exactly by its named market program:
`liaHistory DPH n φ = (MH.quote n ⌜φ⌝ : ℝ)` for `MH := liaMarketComputation DPH hH`. The quote
`⌜𝔼^H_{f n}(XH n)⌝` of `A/Sigma.lean` therefore names a machine (`MH.code`), and `H` is what it
computes.
Source: plan rigor critique 17; [[route-negative-introspective]] §4.3 ("the fixed index of the program computing `H`'s market"); FAF `MarketComputation.quote_exact`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaHistory_eq_machine (DPH : DeductiveProcess) (hH : ComputableDeductiveProcess DPH)
    (n : ℕ) (φ : Sentence) :
    liaHistory DPH n φ = ((liaMarketComputation DPH hH).quote n (Encodable.encode φ) : ℝ) :=
  (liaMarketComputation DPH hH).quote_exact n φ

/-- **T1.2, rational form.** The exact rational LIA quote is the machine's quote.
Source: plan rigor critique 17
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaQuote_eq_machine (DPH : DeductiveProcess) (hH : ComputableDeductiveProcess DPH)
    (n : ℕ) (φ : Sentence) :
    liaQuote DPH n φ = (liaMarketComputation DPH hH).quote n (Encodable.encode φ) := by
  have h := liaHistory_eq_machine DPH hH n φ
  rw [liaHistory_eq_quote_cast] at h
  exact_mod_cast h

/-- **T1.2, expectation form.** `H`'s day-`m` expectation of `X n` is the cast of the machine's
exact rational `expectQuoteAt X n m` (FAF's `expectQuoteAt_cast` at the LIA's program).
Source: plan rigor critique 17; FAF `MarketComputation.expectQuoteAt_cast`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaHistory_expect_eq_machine (DPH : DeductiveProcess)
    (hH : ComputableDeductiveProcess DPH) (X : ℕ → LUV) (n m : ℕ) :
    (X n).expect (liaHistory DPH) m = ((liaMarketComputation DPH hH).expectQuoteAt X n m : ℝ) :=
  (liaMarketComputation DPH hH).expectQuoteAt_cast X n m

/-! ## T1.3: the Σ₁ pair over `paperDP 𝗜𝚺₁` -/

/-- `H`'s process in the witness: `li-quote-lane`'s one-way reader's process — `paperDP 𝗜𝚺₁` plus
the ledger of `A := liaHistory (paperDP 𝗜𝚺₁)`'s day-`n` prices of the atoms `⟨0, ⟨j, n⟩⟩`,
published the next day (`paperOneWayPair.process`, definitionally).
Source: mandate T1.3 (`paperOneWayPair`'s `H`)
Kind: D
Fidelity: n/a -/
noncomputable abbrev witnessHProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) (fun j n => liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
    (fun _ => PublicationSchedule.succ)

/-- The witness's `H`-process is computable (`li-quote-lane` T1.4 at `A`'s LIA table).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessHProcess_computable : ComputableDeductiveProcess witnessHProcess :=
  ledgerProcess_computable (paperDP_computable 𝗜𝚺₁)
    (liaQuote_computable (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) witnessQuoted
      witnessQuoted_computable) succSchedule_computable

/-- `H`'s exact market program in the witness (FAF's `liaMarketComputation`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def witnessMH : MarketComputation (liaHistory witnessHProcess) :=
  liaMarketComputation witnessHProcess witnessHProcess_computable

/-- **T1.3 (N+). The Σ₁ pair over the paper process:** `A = liaHistory (paperDP 𝗜𝚺₁)` (bare paper
LIA), `H = liaHistory witnessHProcess` (the one-way reader of `A`'s prices, `paperOneWayPair.H`),
`XH = cleanX`, `f = succDeferral`; `code` and `package` are `A/Sigma.lean`'s discharge at `H`'s
program `witnessMH`; `hworldA = paperDP_hworld`, `hworldH = ledgerProcess_paperDP_hworld`. Every
field is derived (`(a)`). N+ grounds: `sigmaPair_paper_processes_differ`, `cleanX_tagFree`,
`sigmaPair_paper_both_polarities` below. Scope: one-way in timing, two-way in determinacy.
Source: mandate T1.3; [[faithful-acceleration]] §4(II) (root-fa-002, non-vacuity of the determinacy assumption)
Kind: N+
Fidelity: exact (determinacy); timing: none
Hyps: (a) none -/
noncomputable def sigmaPair_paper : SigmaPair where
  T := 𝗜𝚺₁
  DPH0 := paperDP 𝗜𝚺₁
  quotedA := witnessQuoted
  e := fun _ => PublicationSchedule.succ
  XH := cleanX
  f := succDeferral
  A := liaHistory (paperDP 𝗜𝚺₁)
  A_eq := rfl
  H := liaHistory witnessHProcess
  H_inductor := oneWayPair_inductor (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessQuoted witnessQuoted_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
  MH := witnessMH
  code := sigmaQuoteCode 𝗜𝚺₁ witnessMH cleanX cleanX_codes succDeferral
  package := crossQuotePackage_sigma 𝗜𝚺₁ witnessMH cleanX cleanX_codes succDeferral
  hworldA := paperDP_hworld 𝗜𝚺₁
  hworldH := ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- The witness's `H` is `li-quote-lane`'s one-way reader, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigmaPair_paper_H : sigmaPair_paper.H = paperOneWayPair.H := rfl

/-- The witness's `A` is the bare paper LIA, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigmaPair_paper_A : sigmaPair_paper.A = liaHistory (paperDP 𝗜𝚺₁) := rfl

/-! ### N+ grounds -/

/-- **N+ grounds: the two processes differ.** The affirmed ledger literal of item `j`, day `n` at
threshold `-1` is in some stage of `H`'s process and in no stage of `A`'s process `paperDP 𝗜𝚺₁`
(every sentence of which is cleanroom-free, `paperDP_cleanroomFree`): `H` reads a ledger `A`
does not have.
Source: mandate T1.3 (N+ criteria)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem sigmaPair_paper_processes_differ (j n : ℕ) :
    ∃ s, ∃ φ ∈ witnessHProcess.D s, ∀ k, φ ∉ (paperDP 𝗜𝚺₁).D k := by
  obtain ⟨s, hs⟩ := (ledgerSchedule_both_polarities
    (fun j n => liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n)) (fun _ => PublicationSchedule.succ)
    (fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n)) j n).1
  refine ⟨s, freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode (-1 : ℚ))), ?_, ?_⟩
  · rw [ledgerProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, hs, rfl⟩)
  · intro k hk
    have hfree := paperDP_cleanroomFree 𝗜𝚺₁ k _ hk
    exact hfree.freshAtomCode_notMem ledgerFamily
      (ledgerPayload j n (Encodable.encode (-1 : ℚ))) (by simp [freshAtom])

/-- **N+ grounds: `XH` is outside the ledger family.** No threshold sentence of any `cleanX n`
(`⊤`, `φ ⋏ ∼∼φ` with `φ = ⟨0, ⟨0, n⟩⟩`, or `⊥`) mentions a family-`3` (ledger) atom, so `A`'s
quotation LUVs name `H`'s expectations of sentences no ledger literal touches.
Source: mandate T1.3 (N+ criteria); `li-quote-lane` audit r2 (probe adopted as `cleanX`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem cleanX_tagFree (n : ℕ) (r : ℚ) :
    TagFreeSentence (cleanroomBaseTag + ledgerFamily) ((cleanX n).gt r) := by
  have hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) (witnessQuoted 0 n) := by
    intro a ha
    simp only [witnessQuoted, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    simp [Nat.unpair_pair, cleanroomBaseTag, ledgerFamily]
  show TagFreeSentence _ (if r < 0 then (⊤ : Sentence) else
    if r < 1 then witnessQuoted 0 n ⋏ ∼∼witnessQuoted 0 n else (⊥ : Sentence))
  split_ifs
  · intro a ha
    simp at ha
  · exact hφ.and hφ.neg.neg
  · exact tagFreeSentence_falsum _

/-- **N+ grounds: both polarities occur in `H`'s ledger**, for every item and day (`r = -1`
affirmed, `r = 2` denied).
Source: mandate T1.3 (N+ criteria)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem sigmaPair_paper_both_polarities (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (fun j n => liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
          (fun _ => PublicationSchedule.succ)).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (fun j n => liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
          (fun _ => PublicationSchedule.succ)).lits s :=
  ledgerSchedule_both_polarities _ _ (fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
    j n

/-! ### T1.4 instantiated at the witness -/

/-- **T1.4 at `sigmaPair_paper`, `AffineCombination` approximate form:** the precision-`(n+1)`
mesh of `A`'s quote LUVs is `ApproxDeterminedViaTheory` at `H`'s realized next-day expectations of
`cleanX n`, error `1/(n+1)`, in `paperDP 𝗜𝚺₁`.
Source: mandate T1.4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigmaPair_paper_approxDetermined_mesh :
    AffineCombination.ApproxDeterminedViaTheory
      (fun n => (LUVCombination.ofLUV (sigmaPair_paper.code.luv n)).meshAffine (n + 1))
      sigmaPair_paper.A (paperDP 𝗜𝚺₁)
      (fun n => (cleanX n).expect sigmaPair_paper.H (succDeferral.f n))
      (fun n => 1 / ((n : ℝ) + 1)) :=
  sigmaPair_paper.package.approxDetermined_mesh _

/-- **T1.4 at `sigmaPair_paper`, `LUVCombination` affine-image form:** the affine images
`α · ⌜𝔼^H_{n+1}(cleanX n)⌝ + β` are `DeterminedViaTheory` at `α · 𝔼^H_{n+1}(cleanX n) + β`.
Source: mandate T1.4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sigmaPair_paper_determinedViaTheory_affineImage (α β : ℚ) :
    LUVCombination.DeterminedViaTheory
      (fun n => LUVCombination.affineImage α β (sigmaPair_paper.code.luv n))
      sigmaPair_paper.A (paperDP 𝗜𝚺₁)
      (fun n => α * (cleanX n).expect sigmaPair_paper.H (succDeferral.f n) + β) :=
  DeterminedVia.determinedViaTheory_affineImage α β _ sigmaPair_paper.package.reflected

end Cleanroom.Li.LiCoupledPair.A
