import Cleanroom.Fa.FaTheoremA.LemmaP
import LogicalInduction.Properties.ExpectationConvergence
import Cleanroom.Found.LiAsympCalc.Compactness

/-!
# `fa-theorem-a` · TheoremA: fixed questions are delay-proof (T5)

**Theorem A** ([[faithful-acceleration-result]] §4.2; root-fa-027): for a *fixed* `[0,1]`-LUV
`X` of `H`'s language, an advisor `A` that forecasts `H`'s future expectation
`Y_n := 𝔼^H_{f n}(X)` cannot, for any `c > 0`, advertise `a_n := 𝔼^A_n(⌜Y_n⌝) ≥ 𝔼^H_n(X) + c`
on infinitely many days — with arbitrary delay `f` and zero visibility (`A` never reads `H`'s
prices; `H` never reads `A`'s). Proof shape (the note's): Expectations Converge
(FAF `LUV.expect_converges`, LI 4.8.3) gives `𝔼^H_n(X) → L`; the realized `Y_n → L` as a
subsequence; Lemma P at `E ≡ 1` (`lemmaP_const`, which *is* the note's gate argument —
`Engine.lean`: a persistent violation makes the generable gate `Ind_δ(a_n > q)` divergent and
one-signed, contradicting Half 1's engine) gives `a_n → L`; two sequences with a common limit
dominate each other. The statement is packaged through `li-asymp-calc`'s `Dominates`, `viol`,
`liminf` forms (root-fa-014).

**Three citation repairs the Lean statement makes** against the source
(`fa-block-staleness-impossibility.md`; finding F1): it uses `𝔼^H` (`LUV.expect`), not `ℙ^H`;
it cites Expectations Converge (4.8.3, `LUV.expect_converges`), not sentence convergence (4.1.1);
and the `BLCS` side is carried by `pkg.boundedSequence` (from `quote_codes`).

Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. **Fixed `X`**: the name does not generalize; the varying-question form is
`theoremA_convergentFamily` (`Extensions.lean`, hypotheses on `𝔼^H_n(X n)` and on `Y_n`). The only
modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory determines `H`'s run
outputs, a form of `A` "seeing" `H` logically rather than through prices (root-fa-027); at the
mirror witness it is (a) at variant fidelity (ledger-recorded).
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **The common limit.** Under Theorem A's hypotheses, `𝔼^H_n(X)` and the quote
`a_n = 𝔼^A_n(⌜𝔼^H_{f n}(X)⌝)` converge to one and the same real `L` — the strongest form, from
which `theoremA`, `theoremA_below` and `claim2` read off. `L` is the limit FAF's
`expect_converges` provides; it is not named by the statement (`∃ L`).
Scope: one-way; fixed `X`; the (c) is `pkg.reflected` (see `theoremA`).
Source: [[faithful-acceleration-result]] §4.2 (root-fa-027); [[route-negative-introspective]] §7 (Lemma P at `E = ℕ⁺`)
Kind: C
Fidelity: stronger: a common limit, not only dominance
Hyps: (a) `hcode`, `hworldH`, `hval` (FAF's disclosed boundaries of `thm:ec`; `hval` is FAF's own disclosed linkage), `hworldA`; (c) `pkg.reflected`. -/
theorem theoremA_common_limit {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    ∃ L : ℝ, Tendsto (fun n => X.expect H n) atTop (𝓝 L) ∧
      Tendsto (quoteSeq Y A) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := LUV.expect_converges H DPH X hcode hworldH hval
  have hL' : Tendsto (fun n => X.expect H n) atTop (𝓝 L) := hL
  refine ⟨L, hL', ?_⟩
  exact lemmaP_const pkg hworldA (tendsto_realized_of_tendsto f X hL)

/-- **T5 (headline). Theorem A: fixed questions are delay-proof.** Fix `X : LUV`. For
`[IsLogicalInductor H DPH]` with FAF's `thm:ec` boundaries (`hcode`, `hworldH`, `hval`), any
`[IsLogicalInductor A DPA]` with `hworldA`, any deferral function `f`, and a quote package tying
`⌜Y⌝` to `H`'s realized `𝔼^H_{f n}(X)`: `Dominates (fun n => 𝔼^H_n(X)) (fun n => 𝔼^A_n(Y_n))`,
i.e. **for every `c > 0`, only finitely many `n` have `𝔼^H_n(X) ≤ 𝔼^A_n(⌜𝔼^H_{f n}(X)⌝) − c`**
(`∀ c > 0, ∀ᶠ n in atTop, a_n − c < 𝔼^H_n(X)`; quantifier order `∀ c, ∀ᶠ n`). Proof: the
note's, via `theoremA_common_limit` (Expectations Converge + the subsequence step + Lemma P at
`E ≡ 1`, whose body is the gate argument of `Engine.lean`). Neither `Y_n → L` nor
`𝔼^H_n(X) → L` is a hypothesis — both are derived.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. **Fixed `X`**: the name does not generalize; the varying-question form is
`theoremA_convergentFamily` (hypotheses on `𝔼^H_n(X n)` and on `Y_n`).
The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory determines
`H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[faithful-acceleration-result]] §4.2 Theorem A (root-fa-027 (iii)); vq-wiki-031; lean-deference-052; [[delay-program]] §6 T2
Kind: C
Fidelity: exact (the note's displayed conclusion, in `li-asymp-calc`'s `Dominates`)
Hyps: (a) FAF's `hcode`/`hworldH`/`hval` boundaries of `thm:ec` (`hval` is FAF's own disclosed linkage), `hworldA`; (c) `pkg.reflected` as above. -/
theorem theoremA {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    Dominates (fun n => X.expect H n) (quoteSeq Y A) := by
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A) X hcode hworldH hval hworldA pkg
  exact dominates_of_tendsto hL ha

/-- **T5, the below-gate dual:** for every `c > 0`, only finitely many `n` have
`𝔼^A_n(⌜𝔼^H_{f n}(X)⌝) ≤ 𝔼^H_n(X) − c` (the advisor cannot persistently under-advertise either).
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: [[route-recurring-ccee]] §4 (the dual gate); [[eisenstat-lookahead-construction]] §3.1 (Claim 2's lower half; vq-wiki-058)
Kind: C
Fidelity: exact
Hyps: (a) as `theoremA`; (c) `pkg.reflected`. -/
theorem theoremA_below {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    Dominates (quoteSeq Y A) (fun n => X.expect H n) := by
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A) X hcode hworldH hval hworldA pkg
  exact dominates_of_tendsto ha hL

/-- **Claim 2 (two-sided, per-day Theorem A):** `a_n − 𝔼^H_n(X) → 0`, i.e.
`(fun n => 𝔼^A_n(⌜𝔼^H_{f n}(X)⌝)) ≈ₙ (fun n => 𝔼^H_n(X))` (FAF's `AsympEq`). From Lemma P at
`E ≡ 1` with `c := L` plus Expectations Converge (`theoremA_common_limit`).
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: [[eisenstat-lookahead-construction]] §3.1 ("Claim 2": `a_n − 𝔼^H_n(X) → 0` under arbitrary delay, proved there from Lemma P at `E = ℕ` and 4.8.3; vq-wiki-058); Lemma P itself is [[route-negative-introspective]] §7
Kind: C
Fidelity: exact
Hyps: (a) as `theoremA`; (c) `pkg.reflected`. -/
theorem claim2 {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    AsympEq (quoteSeq Y A) (fun n => X.expect H n) := by
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A) X hcode hworldH hval hworldA pkg
  exact asympEq_of_tendsto ha hL

/-! ## Packaging through `li-asymp-calc` (root-fa-014) -/

/-- **T5, violation-weight form:** for every rational `t`, `ε > 0`, `δ > 0`, the doubly-soft
violation weight `viol (𝔼^H_·(X)) a t ε δ n = Ind_δ(a_n > t)·Ind_δ(𝔼^H_n(X) < t − ε)` tends to
`0` (in fact it is eventually `0`, `Dominates.viol_eventually_zero`).
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: root-fa-014 ([[fa-positive-results-corrected-v2]] §5.5's packaging); `li-asymp-calc` E1
Kind: L
Fidelity: exact
Hyps: (a) as `theoremA`; (c) `pkg.reflected`. -/
theorem theoremA_viol_tendsto {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y)
    (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    Tendsto (viol (fun n => X.expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) :=
  (theoremA (A := A) X hcode hworldH hval hworldA pkg).tendsto_viol t hε hδ

/-- **T5, summable form:** the violation weights are summable.
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: root-fa-014; `li-asymp-calc` E1
Kind: L
Fidelity: exact
Hyps: (a) as `theoremA`; (c) `pkg.reflected`. -/
theorem theoremA_summable {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y)
    (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    Summable (viol (fun n => X.expect H n) (quoteSeq Y A) t ε δ) :=
  (theoremA (A := A) X hcode hworldH hval hworldA pkg).summable_viol t hε hδ

/-- **T5, liminf form:** `0 ≤ liminf (𝔼^H_n(X) − a_n)` (via `dominates_iff_liminf`, which needs
`[0,1]`-valuedness: FAF's `LUV.expect_mem_Icc` and `IsLogicalInductor.price_mem_Icc` on both
markets).
Scope: one-way; fixed `X`; the (c) is `pkg.reflected`.
Source: root-fa-014; `li-asymp-calc` E1 (`dominates_iff_liminf`)
Kind: L
Fidelity: exact
Hyps: (a) as `theoremA`; (c) `pkg.reflected`. -/
theorem theoremA_liminf {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y) :
    0 ≤ liminf (fun n => X.expect H n - quoteSeq Y A n) atTop := by
  have ha : ∀ n, quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (DP := DPA) n s)
  have he : ∀ n, X.expect H n ∈ Set.Icc (0 : ℝ) 1 := fun n =>
    LUV.expect_mem_Icc H n X (fun s => IsLogicalInductor.price_mem_Icc (DP := DPH) n s)
  exact (dominates_iff_liminf ha he).1 (theoremA (A := A) X hcode hworldH hval hworldA pkg)

end Cleanroom.Fa.FaTheoremA
