import Cleanroom.Fa.FaTheoremA.TheoremA
import LogicalInduction.Construction.LUV.Endpoints

/-!
# `fa-theorem-a` · Decided: the fixed-member diagonal is the decided case of Theorem A (T7)

root-fa-2-006: "the fixed-`X` statement is true and nearly empty there" — on a LUV `X` that
`H`'s process *determines* at a value `v` (`LUV.DeterminedVia X DPH v`; the note's "decided" is
the `{0,1}` case, but any determined value works and nothing below needs `v ∈ {0,1}`), Theorem
A's conclusions are exercised with every hypothesis discharged: `𝔼^H_n(X) → v` (FAF's
combination-level expectation provability induction
`lic_expect_combination_provind_eq_ofDetermined` on `ofLUV X`; this replaces `hval` and
`expect_converges` on `H`'s side — FAF also has the single-LUV forms `lic_expectation_provind` /
`_ofValuesAt` / `_le` / `_eq` (`Properties/ExpectationAffine.lean:675/706/720/752`), whose value
hypotheses are *stage-indexed* (`∀ v, v.ConsistentWith (DP.D n) → …`, eventually in `n`); the
package's hypothesis is the completed-theory `DeterminedVia`, which `li-asymp-calc` bridges to
`DeterminedViaTheory`, the input of the combination form, hence the choice), hence the realized
`Y_n → v`, the quote `a_n → v` (Lemma P at
`E ≡ 1`), and every violation weight is eventually `0` in both directions: violations are
confined to finitely many early days. The diagonal member `g_m` itself is `li-diagonal`'s
(root-fa-037); this file states the decided case for an arbitrary determined `X`.

Scope: one-way; fixed `X`; the only modelling step is `pkg.reflected` (`Half1.lean`).
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- A single LUV's e.c. certificate, as the constant family's (`MachineThresholdCodeSeq` of
`fun _ => X` from `MachineThresholdCodes X`, by precomposition with the second unpairing).
Source: none: infrastructure (FAF `MachineSentenceCodes.comp`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma machineThresholdCodeSeq_const {X : LUV} (h : X.MachineThresholdCodes) :
    LUV.MachineThresholdCodeSeq (fun _ => X) :=
  (MachineSentenceCodes.comp h UnaryRuler.unpairSnd).of_eq (fun _ => rfl)

/-- The converse: the constant family's certificate gives the single LUV's (precomposition with
`m ↦ ⟨0, m⟩`).
Source: none: infrastructure (FAF `MachineSentenceCodes.comp`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma machineThresholdCodes_of_const_seq {X : LUV}
    (h : LUV.MachineThresholdCodeSeq (fun _ => X)) : X.MachineThresholdCodes :=
  (MachineSentenceCodes.comp h ((UnaryRuler.const 0).pair UnaryRuler.id)).of_eq
    (fun m => by simp)

/-- The singleton combination `0 + 1·X` is a `BoundedSequence` in any market, from `X`'s e.c.
certificate (`li-quote-lane`'s `ofLUV_mesh_polySequence` at the constant family; `L¹` bound `1`).
Source: none: infrastructure (`li-quote-lane` `CrossQuotePackage.boundedSequence` at a constant family)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
noncomputable def boundedSequence_ofLUV_const (X : LUV) (hcode : X.MachineThresholdCodes)
    (P : History) : LUVCombination.BoundedSequence (fun _ => LUVCombination.ofLUV X) P where
  poly := ⟨ofLUV_mesh_polySequence (fun _ => X) (machineThresholdCodeSeq_const hcode)⟩
  bounded := ⟨1, fun _ => (l1Norm_ofLUV X P).2.le⟩

/-- **T7 (i). A determined LUV's expectations converge to its determined value**:
`𝔼^H_n(X) → v` from `LUV.DeterminedVia X DPH v`, by FAF's
`lic_expect_combination_provind_eq_ofDetermined` on `ofLUV X` (with `li-asymp-calc`'s
determinacy bridges). This is the `H`-side input of Theorem A with `hval` and
`expect_converges` replaced by the determinacy — and the limit *named*.
Source: root-fa-2-006 ("the fixed-`X` statement is true and nearly empty there"); FAF `thm:expprovind` — the combination-level form over `ofLUV` is used because its input `DeterminedViaTheory` is what `DeterminedVia` bridges to; FAF's single-LUV `lic_expectation_provind`/`_eq` (`Properties/ExpectationAffine.lean:675/752`, stage-indexed value hypotheses) exist and root-fa-2-006's citation of them stands (the mandate's Known issue 9 and plan §0.4 rule 5 say otherwise and are wrong; F11)
Kind: C
Fidelity: exact
Hyps: (a) `hcode`, `hworldH`, `hdec` (FAF's disclosed boundaries) -/
theorem decided_expect_tendsto {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {v : ℝ}
    (hdec : LUV.DeterminedVia X DPH v) :
    Tendsto (fun n => X.expect H n) atTop (𝓝 v) := by
  have h := lic_expect_combination_provind_eq_ofDetermined (boundedSequence_ofLUV_const X hcode H)
    (DeterminedVia.worldValued_ofLUV (X := fun _ => X) (y := fun _ => v) (fun _ => hdec))
    (DeterminedVia.determinedViaTheory_ofLUV (X := fun _ => X) (y := fun _ => v) H
      (fun _ => hdec)) v (fun _ => rfl) hworldH
  have h' : ConvergesTo (fun n => (LUVCombination.ofLUV X).expect H n) v :=
    convergesTo_iff_asympEq_const.2 h
  simpa only [ofLUV_expect] using h'

/-- **T7 (ii).** The realized `Y_n = 𝔼^H_{f n}(X) → v` for a determined `X`.
Source: root-fa-2-006
Kind: L
Fidelity: exact
Hyps: (a) as `decided_expect_tendsto` -/
theorem decided_realized_tendsto {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {v : ℝ}
    (hdec : LUV.DeterminedVia X DPH v) (f : DeferralFunction) :
    Tendsto (realized H f (fun _ => X)) atTop (𝓝 v) :=
  tendsto_realized_of_tendsto f X (decided_expect_tendsto X hcode hworldH hdec)

/-- **T7 (iii), headline. The decided case of Theorem A:** for a LUV `X` determined by `H`'s
process at `v`, the quote `a_n = 𝔼^A_n(⌜𝔼^H_{f n}(X)⌝) → v` (Lemma P at `E ≡ 1`), alongside
`𝔼^H_n(X) → v` — every hypothesis of Theorem A discharged on a determined target, with the
common limit named. Exercised with content at `Witnesses.lean` W2 (an atom-deciding `H`).
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. **Fixed `X`**: the name does not generalize; the varying-question form is
`theoremA_convergentFamily`. The only modelling step is the quote's determinacy,
`pkg.reflected` — `A`'s theory determines `H`'s run outputs, a form of `A` "seeing" `H`
logically rather than through prices (root-fa-027); at the mirror witness it is (a) at variant
fidelity (ledger-recorded).
Source: root-fa-2-006; [[fa-positive-result-corrected]] §6 (the fixed-member diagonal)
Kind: C
Fidelity: exact (any determined value, not only `{0,1}`)
Hyps: (a) `hcode`, `hworldH`, `hdec`, `hworldA`; (c) `pkg.reflected`. -/
theorem decided_quote_tendsto {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {v : ℝ}
    (hdec : LUV.DeterminedVia X DPH v)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    Tendsto (quoteSeq Y A) atTop (𝓝 v) :=
  lemmaP_const (A := A) pkg hworldA (decided_realized_tendsto X hcode hworldH hdec f)

/-- **T7 (iv). Violations are confined to finitely many early days**, in both directions: for
every rational `t`, `ε > 0`, `δ > 0`, the violation weights `viol (𝔼^H_·(X)) a t ε δ` and
`viol a (𝔼^H_·(X)) t ε δ` are eventually `0`.
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: root-fa-2-006; root-fa-014 (`Dominates.viol_eventually_zero`)
Kind: L
Fidelity: exact
Hyps: (a) as `decided_quote_tendsto`; (c) `pkg.reflected`. -/
theorem decided_viol_eventually_zero {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) {v : ℝ}
    (hdec : LUV.DeterminedVia X DPH v)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y)
    (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∀ᶠ n in atTop, viol (fun n => X.expect H n) (quoteSeq Y A) t ε δ n = 0) ∧
      (∀ᶠ n in atTop, viol (quoteSeq Y A) (fun n => X.expect H n) t ε δ n = 0) := by
  have he := decided_expect_tendsto (H := H) X hcode hworldH hdec
  have ha := decided_quote_tendsto (A := A) X hcode hworldH hdec hworldA pkg
  exact ⟨(dominates_of_tendsto he ha).viol_eventually_zero t hε hδ,
    (dominates_of_tendsto ha he).viol_eventually_zero t hε hδ⟩

end Cleanroom.Fa.FaTheoremA
