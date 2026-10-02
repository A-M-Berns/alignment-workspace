import Cleanroom.Fa.FaTheoremA.TheoremA
import LogicalInduction.Properties.TimelyLearning

/-!
# `fa-theorem-a` · Extensions: varying questions (T11, OP8/OP16) and the calibration route (T10)

* **T11 — varying-but-convergent questions (OP8).** `theoremA_convergentFamily`: for a family
  `X : ℕ → LUV`, with *both* `𝔼^H_n(X n) → p` and the realized `Y_n = 𝔼^H_{f n}(X n) → p` as the
  statement's own antecedents, Theorem A's conclusions hold verbatim (`Dominates` and the
  two-sided `≈ₙ`). The note's "`𝔼^H_n(X_{k(n)}) → p_∞` for a single limit across blocks" is
  ambiguous (finding F6): convergence of the diagonal alone does not give `Y_n → p`; the reading
  the proof needs has both. `hY` alone already gives `a_n → p` (`lemmaP_const`).
* **The convergence-free form (OP16, answered in a sharper form).** Route A gives, with no
  convergence hypothesis at all, the **limit-range squeeze** on `A`'s side:
  `liminf Y_n ≤ liminf a_n` and `limsup a_n ≤ limsup Y_n`
  (`liminf_realized_le_liminf_quote`, `limsup_quote_le_limsup_realized`) — the quote's limit range
  sits inside the realized values' limit range, for *any* e.c. family, arbitrary delay, zero
  visibility. The convergence-free Theorem A is then `theoremA_limitRange`: the quote's limit
  range sits inside the diagonal's, **given** the no-surprise inclusion `Y`-range ⊆ `e`-range
  (`hlo`, `hhi`). That inclusion is exactly what convergence supplied, and **FAF's 4.8.12/4.8.13
  go the other way** (`BoundedSequence.exppolymax`: `liminf 𝔼_n(B_n) = liminf futureHigh`,
  `limsup 𝔼_n(B_n) = limsup futureLow`, with `futureLow n ≤ Y_n ≤ futureHigh n`, gives
  `e`-range ⊆ `Y`-range — the diagonal cannot be more extreme than the future, but the future
  may be more extreme than the diagonal). So the route OP16 proposes does not go through:
  4.8.12/4.8.13 point the wrong way (proved, from FAF's own statements) and do not replace
  convergence *as stated*. What the convergence-free form needs is the no-surprise inclusion.
  Whether some `H`-side hypothesis weaker than convergence yields it, and whether the per-day
  conclusion can actually *fail* for a non-convergent `H`, are conjectured (no, resp. yes) and
  not refuted here: a refutation needs an `H` that learns `X_n` between day `n` and day `f n`,
  i.e. LIA price pinning (finding F7). The dividing line is surprise, not variation — made
  precise on the proved side.
* **T10 — the Recurring-Calibration route to Half 1** (vq-wiki-043 (b), untried in the corpus).
  `calibration_route`: FAF's `thm:simcal` (`simcal_of_recurring_unbiasedness` over the
  sentence-level `recurringunbiasedness`) on `A`'s market at the threshold sentences
  `⌜Y_n > i/k⌝` with the band gate `calibrationIndicator`: on the days `A` prices `⌜Y_n > i/k⌝`
  in `(a, b)`, the frequency with which `H`'s realized value really ends above `i/k` has a limit
  point in `[a, b]`, and every global limit lies there — two-sided. **Junk-value guard** (finding
  F10): `TheoryTruth` of the threshold sentence needs `Y_n ≠ i/k` for every `n` (`hne`), since a
  threshold equal to the value is unconstrained by `PCWorld.ValuesAt`; for `X` with rational
  expectations it can fail. Calibration is gameable and weaker than unbiasedness (the corpus's
  warning): Half 1 proper is T3.

Scope: one-way throughout; the only modelling step is `pkg.reflected` (`Half1.lean`).
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. Bounds -/

/-- The realized sequence is `[0,1]`-valued: from `pkg.reflected` (FAF's `ValuesAt` carries the
bounds) at a completed-theory world, which `hworldA` provides by compactness.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) `hworldA`; (c) `pkg.reflected` -/
theorem realized_mem_Icc {H : History} {DPA : DeductiveProcess} {f : DeferralFunction}
    {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (n : ℕ) :
    realized H f X n ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨v, hv⟩ := DeductiveProcess.exists_consistentWithTheory _ hworldA
  have h := pkg.reflected n v hv
  exact ⟨h.1, h.2.1⟩

/-- The quote is `[0,1]`-valued (FAF's price bounds).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quote_mem_Icc {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (Y : ℕ → LUV) (n : ℕ) : quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 :=
  LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (DP := DPA) n s)

/-! ## B. The convergence-free form: the limit-range squeeze on `A`'s side -/

/-- **`limsup a_n ≤ limsup Y_n`, with no convergence hypothesis.** Route A: if
`limsup Y + η < limsup a`, the quote exceeds `limsup Y + η/2` infinitely often while `Y_n` is
eventually below `limsup Y + η/4`; `not_frequently_quote_ge` at `E ≡ 1` contradicts.
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[open-problems]] item 16 (vq-wiki-032), answered in the limit-range form; [[route-negative-introspective]] §7 (Lemma P without convergence)
Kind: C
Fidelity: stronger: Lemma P at `E ≡ 1` without a limit
Hyps: (a) `hworldA`; (c) `pkg.reflected`. -/
theorem limsup_quote_le_limsup_realized {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    limsup (quoteSeq Y A) atTop ≤ limsup (realized H f X) atTop := by
  have hY01 := realized_mem_Icc pkg hworldA
  have ha01 := quote_mem_Icc (A := A) (DPA := DPA) Y
  by_contra hlt
  have hlt' : limsup (realized H f X) atTop < limsup (quoteSeq Y A) atTop := not_le.1 hlt
  have hYbdd : IsBoundedUnder (· ≤ ·) atTop (realized H f X) :=
    isBoundedUnder_of ⟨1, fun n => (hY01 n).2⟩
  have hacobdd : IsCoboundedUnder (· ≤ ·) atTop (quoteSeq Y A) :=
    (isBoundedUnder_of ⟨0, fun n => (ha01 n).1⟩ :
      IsBoundedUnder (· ≥ ·) atTop (quoteSeq Y A)).isCoboundedUnder_le
  set LY := limsup (realized H f X) atTop with hLY
  set La := limsup (quoteSeq Y A) atTop with hLa
  have hfreq : ∃ᶠ n in atTop, LY + (La - LY) / 2 < quoteSeq Y A n :=
    frequently_lt_of_lt_limsup hacobdd (by linarith)
  have hev : ∀ᶠ n in atTop, realized H f X n < LY + (La - LY) / 4 :=
    eventually_lt_of_limsup_lt (by linarith) hYbdd
  refine not_frequently_quote_ge (A := A) pkg hworldA (pgenerableWeighting_const 1)
    (fun _ => Or.inr (by simp)) (u := LY + (La - LY) / 4) (η := (La - LY) / 4)
    (by linarith) ?_ ?_
  · exact hev.mono (fun n hn _ => hn.le)
  · exact hfreq.mono (fun n hn => ⟨by simp, by linarith⟩)

/-- **`liminf Y_n ≤ liminf a_n`, with no convergence hypothesis** (the dual).
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[open-problems]] item 16 (vq-wiki-032); [[route-negative-introspective]] §7
Kind: C
Fidelity: stronger: Lemma P at `E ≡ 1` without a limit
Hyps: (a) `hworldA`; (c) `pkg.reflected`. -/
theorem liminf_realized_le_liminf_quote {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    liminf (realized H f X) atTop ≤ liminf (quoteSeq Y A) atTop := by
  have hY01 := realized_mem_Icc pkg hworldA
  have ha01 := quote_mem_Icc (A := A) (DPA := DPA) Y
  by_contra hlt
  have hlt' : liminf (quoteSeq Y A) atTop < liminf (realized H f X) atTop := not_le.1 hlt
  have hYbdd : IsBoundedUnder (· ≥ ·) atTop (realized H f X) :=
    isBoundedUnder_of ⟨0, fun n => (hY01 n).1⟩
  have hacobdd : IsCoboundedUnder (· ≥ ·) atTop (quoteSeq Y A) :=
    (isBoundedUnder_of ⟨1, fun n => (ha01 n).2⟩ :
      IsBoundedUnder (· ≤ ·) atTop (quoteSeq Y A)).isCoboundedUnder_ge
  set LY := liminf (realized H f X) atTop with hLY
  set La := liminf (quoteSeq Y A) atTop with hLa
  have hfreq : ∃ᶠ n in atTop, quoteSeq Y A n < La + (LY - La) / 2 :=
    frequently_lt_of_liminf_lt hacobdd (by linarith)
  have hev : ∀ᶠ n in atTop, LY - (LY - La) / 4 < realized H f X n :=
    eventually_lt_of_lt_liminf (by linarith) hYbdd
  refine not_frequently_quote_le (A := A) pkg hworldA (pgenerableWeighting_const 1)
    (fun _ => Or.inr (by simp)) (u := LY - (LY - La) / 4) (η := (LY - La) / 4)
    (by linarith) ?_ ?_
  · exact hev.mono (fun n hn _ => hn.le)
  · exact hfreq.mono (fun n hn => ⟨by simp, by linarith⟩)

/-- **The convergence-free Theorem A (OP16, sharpened).** For *any* family `X : ℕ → LUV`
(arbitrary delay, zero visibility): if the realized values' limit range sits inside the
diagonal's — `liminf 𝔼^H_n(X n) ≤ liminf Y_n` and `limsup Y_n ≤ limsup 𝔼^H_n(X n)`, the
**no-surprise** inclusion — then so does the quote's: `liminf 𝔼^H_n(X n) ≤ liminf a_n` and
`limsup a_n ≤ limsup 𝔼^H_n(X n)`. The antecedents are the statement's own; convergence of the
diagonal and of `Y_n` to one limit implies them (T11). They are *not* derivable from FAF's
4.8.12/4.8.13, which give the reverse inclusion (module docstring). Kind L: the content is in
the two squeeze lemmas; this is their composition with the statement's own antecedents. The
diagonal `𝔼^H_n(X n)` carries no bound here (`H` is an arbitrary `History`): for an inductor
`H` it lies in `[0,1]` (FAF's `LUV.expect_mem_Icc`), the intended instance; for a wild `H`
Mathlib's `liminf`/`limsup` of an unbounded sequence are junk and only `hlo`/`hhi` give them
meaning.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is `pkg.reflected` (`Half1.lean`).
Source: [[open-problems]] item 16 (vq-wiki-032); [[faithful-acceleration-result]] §4.2 Extension ("the dividing line is surprise, not variation")
Kind: L
Fidelity: variant: liminf/limsup inclusion in place of per-day dominance (which needs convergence)
Hyps: (a) `hworldA`, `hlo`, `hhi` (the statement's antecedents); (c) `pkg.reflected`. -/
theorem theoremA_limitRange {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hlo : liminf (fun n => (X n).expect H n) atTop ≤ liminf (realized H f X) atTop)
    (hhi : limsup (realized H f X) atTop ≤ limsup (fun n => (X n).expect H n) atTop) :
    liminf (fun n => (X n).expect H n) atTop ≤ liminf (quoteSeq Y A) atTop ∧
      limsup (quoteSeq Y A) atTop ≤ limsup (fun n => (X n).expect H n) atTop :=
  ⟨hlo.trans (liminf_realized_le_liminf_quote pkg hworldA),
    (limsup_quote_le_limsup_realized pkg hworldA).trans hhi⟩

/-! ## C. T11: varying-but-convergent questions -/

/-- **T11. Theorem A for a varying-but-convergent family (OP8).** For `X : ℕ → LUV`, with both
`𝔼^H_n(X n) → p` (`hdiag`) and the realized `Y_n = 𝔼^H_{f n}(X n) → p` (`hY`) as antecedents:
`Dominates (fun n => 𝔼^H_n(X n)) (fun n => 𝔼^A_n(Y_n))` and the two-sided
`(fun n => 𝔼^A_n(Y_n)) ≈ₙ (fun n => 𝔼^H_n(X n))`. The proof is Theorem A's verbatim
(`lemmaP_const` on `hY`, then the common limit). `hY` is not implied by `hdiag` (finding F6);
`hY` alone gives `a_n → p`.
Scope: one-way; the only modelling step is `pkg.reflected`. Not named `theoremA`: the fixed-`X`
theorem is `theoremA`; this is its varying-question form with explicit convergence antecedents.
Source: [[eisenstat-lookahead-construction]] §3.2 (the two-antecedent reading, verbatim: "If the realized targets converge … If in addition the human's diagonal credence converges to the same value … then `a_n − 𝔼^H_n(X_n) → 0`"); vq-wiki-032; [[open-problems]] item 8; [[faithful-acceleration-result]] §4.2 Extension; [[delay-program]] §6 T2′
Kind: C
Fidelity: variant: both convergences are antecedents (FAR §4.2 / OP8 state one, ambiguously; ELC §3.2 already states both)
Hyps: (a) `hworldA`, `hdiag`, `hY` (the statement's antecedents); (c) `pkg.reflected`. -/
theorem theoremA_convergentFamily {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {p : ℝ}
    (hdiag : Tendsto (fun n => (X n).expect H n) atTop (𝓝 p))
    (hY : Tendsto (realized H f X) atTop (𝓝 p)) :
    Dominates (fun n => (X n).expect H n) (quoteSeq Y A) ∧
      AsympEq (quoteSeq Y A) (fun n => (X n).expect H n) := by
  have ha := lemmaP_const (A := A) pkg hworldA hY
  exact ⟨dominates_of_tendsto hdiag ha, asympEq_of_tendsto ha hdiag⟩

/-! ## D. T10: the Recurring-Calibration route -/

/-- The threshold sentences `⌜Y_n > i/k⌝` of the quote family (the Boolean form of the quote:
"`H` ends above `i/k`").
Source: vq-wiki-043 (b)
Kind: D
Fidelity: exact
Hyps: n/a -/
def quoteThreshold (Y : ℕ → LUV) (i k : ℕ) (n : ℕ) : Sentence := (Y n).gt ((i : ℚ) / (k : ℚ))

/-- The threshold sentences are e.c., from the quote family's certificate (`quote_codes` at the
index `n ↦ ⟨n, ⟨k, i⟩⟩`).
Source: vq-wiki-043 (b); FAF `MachineThresholdCodeSeq`
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma quoteThreshold_codes (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (i k : ℕ) :
    MachineSentenceCodes (quoteThreshold Y i k) :=
  (MachineSentenceCodes.comp hY
    (UnaryRuler.id.pair ((UnaryRuler.const k).pair (UnaryRuler.const i)))).of_eq
    (fun n => by simp [quoteThreshold])

/-- The truth value of `⌜Y_n > i/k⌝` in every completed-theory world of `A`'s process:
`1` if `i/k < Y_n`, else `0` (meaningful only off the threshold, `thresholdTruth_theoryTruth`).
Source: vq-wiki-043 (b)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def thresholdTruth (H : History) (f : DeferralFunction) (X : ℕ → LUV) (i k : ℕ)
    (n : ℕ) : ℝ :=
  if ((((i : ℚ) / (k : ℚ) : ℚ)) : ℝ) < realized H f X n then 1 else 0

/-- **`TheoryTruth` of the threshold sentences, off the threshold.** From `pkg.reflected`
(`PCWorld.ValuesAt`): a threshold strictly below the value is affirmed, strictly above denied;
**a threshold equal to the value is unconstrained**, hence the guard `hne` (finding F10).
Source: vq-wiki-043 (b); FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: exact (with the junk-value guard disclosed)
Hyps: (a) `hne`; (c) `pkg.reflected` -/
theorem thresholdTruth_theoryTruth {H : History} {DPA : DeductiveProcess} {f : DeferralFunction}
    {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y) (i k : ℕ)
    (hne : ∀ n, realized H f X n ≠ ((((i : ℚ) / (k : ℚ) : ℚ)) : ℝ)) :
    AffineCombination.TheoryTruth (quoteThreshold Y i k) DPA (thresholdTruth H f X i k) := by
  intro n v hv
  have h := (pkg.reflected n v hv).2.2 ((i : ℚ) / (k : ℚ))
  unfold thresholdTruth PCWorld.payout quoteThreshold
  rcases lt_trichotomy ((((i : ℚ) / (k : ℚ) : ℚ)) : ℝ) (realized H f X n) with hlt | heq | hgt
  · rw [if_pos (h.1 hlt), if_pos hlt]
  · exact absurd heq.symm (hne n)
  · rw [if_neg (h.2 hgt), if_neg (not_lt.2 hgt.le)]

/-- **T10. The Recurring-Calibration route to Half 1** (vq-wiki-043 (b), untried in the corpus).
In the context of T3, for naturals `i k` (the threshold `i/k`), the junk-value guard `hne`, a
band `(a, b)` and a positive rational width `δ`, if the band gate
`calibrationIndicator (⌜Y_· > i/k⌝) a b δ` is divergent in `A`'s prices: the gate-weighted
frequency with which `H`'s realized value really ends above `i/k` has a limit point in `[a, b]`,
and every global limit of it lies in `[a, b]` — two-sided. FAF's `thm:simcal`
(`simcal_of_recurring_unbiasedness`) over the sentence-level `recurringunbiasedness` at the
e.c. threshold sentences (`quoteThreshold_codes`) with `TheoryTruth` from `pkg.reflected`.
Weaker than unbiasedness (calibration is gameable); Half 1 proper is T3.
**Junk corners of the threshold** (disclosed, not excluded): at `k = 0` Lean's `i/0 = 0`, so
every `i` names the threshold `0` and `hne` reads `∀ n, Y_n ≠ 0`; at `i/k > 1` the truth stream
is identically `0` (`Y_n ∈ [0,1]`, `realized_mem_Icc`), `hne` holds automatically, and the
conclusion says only that `0 ∈ [a,b]` when the band gate is divergent — true, not calibration.
The intended thresholds are `0 < k` and `0 < i < k`; the statement is true at every `i k`.
Scope: one-way; the (c) is `pkg.reflected`.
Source: vq-wiki-043 (b); [[unbiasedness-theorem-families]] §1–§3 (family A); FAF `thm:simcal`
Kind: C
Fidelity: variant: threshold `i/k` with `i k : ℕ` (nonnegative rationals; junk at `k = 0` and trivial above `1`, as above), and the guard `hne`
Hyps: (a) `hworldA`, `hdiv`, `hne` (the junk-value guard; for `X` with rational expectations it can fail); (c) `pkg.reflected`. -/
theorem calibration_route {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (i k : ℕ)
    (hne : ∀ n, realized H f X n ≠ ((((i : ℚ) / (k : ℚ) : ℚ)) : ℝ)) (a b : ℚ) {δ : ℚ}
    (hδ : 0 < δ)
    (hdiv : DivergentWeighting (calibrationIndicator (quoteThreshold Y i k) a b (fun _ => δ)) A) :
    HasLimitPointIn
        (weightedAverage
          (fun n => (calibrationIndicator (quoteThreshold Y i k) a b (fun _ => δ) n).denote A)
          (thresholdTruth H f X i k)) (Set.Icc (a : ℝ) (b : ℝ)) ∧
      ∀ x, ConvergesTo
          (weightedAverage
            (fun n => (calibrationIndicator (quoteThreshold Y i k) a b (fun _ => δ) n).denote A)
            (thresholdTruth H f X i k)) x →
        x ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  have hφ := quoteThreshold_codes Y pkg.quote_codes i k
  have hδR : ∀ n : ℕ, (0 : ℝ) < ((fun _ : ℕ => δ) n : ℚ) := fun _ => by exact_mod_cast hδ
  have hW : PGenerableWeighting (calibrationIndicator (quoteThreshold Y i k) a b (fun _ => δ)) :=
    calibrationIndicator_pgenerable _ a b _ hφ ⟨MachineRatCodes.const δ, hδR⟩
  have hbias := AffineCombination.recurringunbiasedness (quoteThreshold Y i k)
    (AffineCombination.sentenceAffine_polySequence _ hφ) hW
    (thresholdTruth_theoryTruth pkg i k hne) hdiv hworldA
  exact simcal_of_recurring_unbiasedness A (quoteThreshold Y i k) (thresholdTruth H f X i k) a b
    (fun _ => δ) hδR (fun n => by unfold thresholdTruth; split_ifs <;> simp) hdiv hbias

end Cleanroom.Fa.FaTheoremA
