import Cleanroom.Fa.FaTheoremA.Decided
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Li.LiPseudorandom.Market

/-!
# `fa-theorem-a` · Witnesses: the N+ instances (W1–W3)

The only file of the package allowed to import `li-quote-lane`'s `Witnesses`/`MirrorPair`,
`li-pseudorandom`'s `Market` and (through them) FAF's `LIACompiler`.

* **W1 — Theorem A's full package, two markets.** `H := liaHistory (paperDP 𝗜𝚺₁)`, the fixed
  LUV `X₀ := LUV.indicatorOf (witnessQuoted 0 0)` (an indicator of a tag-`0` base atom of `H`'s
  language), `A := liaHistory` over the mirror ledger of `H`'s realized next-day expectations of
  `X₀` (`li-quote-lane`'s `crossQuotePackage_mirror`, published two days later). Every hypothesis
  of `theoremA` is discharged (`theoremA_w1`). Grade **N−**: the instance is real (two distinct
  LIA markets, a genuine forecast — `cleanMirror_forecast`'s pattern) but non-degeneracy in the
  mandate's sense (a day with `X₀.expect H m ≠ X₀.expect H (m+1)`, or `a_n ≠ Y_n`) is not
  proved: LIA prices of an undecided atom are not pinned by anything in FAF or the dependencies.
* **W2 — the decided case (T7), with content.** `H := liaHistory (atomDP id x (·+1))` for any
  primitive recursive stream `x` (`li-pseudorandom`'s `atomDP_succ_isLogicalInductor`), which
  decides `atom k` at stage `k + 1` with truth `x k`; `X₀ := LUV.indicatorOf (atom k)`, so
  `LUV.DeterminedVia X₀ _ (truthR x k)` is *derived* (`w2_determined`, from
  `atomDP_theoryTruth`), and `A` the mirror ledger over `paperDP 𝗜𝚺₁`. Every hypothesis of T7 is
  discharged and its conclusions are exercised with the limit named (`decided_w2`). Grade
  **N+**: a family of instances over all primitive recursive `x` and all `k` — non-constant
  streams included — on two distinct real LIA markets.
* **W3 — Half 1's divergent gate, at the market level.** The mandate expected only an
  analysis-layer witness; the decided case gives more: at W2 with `x k = true`, the quote
  `a_n → 1`, so the gate `Ind_{1/4}(a_n > 1/2)` of `A`'s own quote *is* divergent in `A`'s realized
  prices (`w3_hdiv`, via the general sufficient condition
  `divergentWeighting_quoteRampAbove_of_tendsto`), and T3 applies with every hypothesis
  discharged (`half1_w3`). Grade: **N+ for the hypothesis package** (two real LIA markets, a
  derived package, a divergent gate exhibited), **N− for T3's content**: the gate is eventually
  identically `1` (`w3_gate_eventually_one`) — it selects every late day and does no selecting —
  and both `a_n` and `Y_n` tend to `1`, so the limit point follows from `decided_w2` by
  `li-asymp-calc`'s donor rule alone (`half1_w3_from_convergence`), with no use of unbiasedness
  on the gate. A *selecting* instance (the quote oscillating across `t` on an undecided target)
  needs LIA price pinning, as W1's grade explains (F15).
* **W4 — Lemma P's day-set.** `E ≡ 1` is `lemmaP_const` (used by every theorem above). The even
  days are a non-trivial generable `{0,1}` day-set (`evenDays_pgenerable`, `LemmaP.lean`: FAF's
  `MachineSpliceStream.ifZero` on the parity ruler, not a `MachineRatCodes` certificate), and
  `lemmaP_w4` instantiates Lemma P at W2 along them. Grade: **N+ for the hypothesis package** (a
  non-constant generable `E`, real markets), **N− for the content**: the along-`E` limit also
  follows from the all-days limit `decided_w2`; a day-set on which `Y_n` converges but off
  which it does not needs an undecided target (F16).

Fidelity of the quote package at every witness: `variant` (ledger-recorded determinacy in place
of `Γ_A`-provable determinacy), copied from `li-quote-lane`'s row.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## Indicator LUVs: e.c. and world-valued -/

/-- A single indicator LUV is e.c. (FAF's `indicatorOf_machineThresholdCodeSeq` at the constant
sentence family, pulled back to the single-LUV certificate).
Source: none: infrastructure (FAF `indicatorOf_machineThresholdCodeSeq`, `MachineSentenceCodes.const`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma indicatorOf_machineThresholdCodes (φ : Sentence) :
    (LUV.indicatorOf φ).MachineThresholdCodes :=
  machineThresholdCodes_of_const_seq
    (LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const φ))

/-- Every completed-theory world values an indicator LUV (at its payout): the `hval` input of
`expect_converges`, discharged by FAF's `indicatorOf_isIndicator`.
Source: none: infrastructure (FAF `LUV.indicatorOf_isIndicator`, `IsIndicator.valuesAt`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma indicatorOf_valued (φ : Sentence) (DP : DeductiveProcess) :
    ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt (LUV.indicatorOf φ) x :=
  fun _ hv => ⟨_, (LUV.indicatorOf_isIndicator φ DP).valuesAt hv⟩

/-! ## W1: Theorem A over `paperDP 𝗜𝚺₁` and the mirror ledger -/

/-- W1's fixed LUV: the indicator of the tag-`0` base atom `witnessQuoted 0 0` of `H`'s language.
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1X : LUV := LUV.indicatorOf (witnessQuoted 0 0)

/-- W1's `H`: FAF's LIA over `paperDP 𝗜𝚺₁`.
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1H : History := liaHistory (paperDP 𝗜𝚺₁)

/-- W1's `A`-process: `paperDP 𝗜𝚺₁` plus the ledger of `H`'s realized day-`(n+1)` expectations
of `w1X`, published at `n + 2`.
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1Process : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) (realizedExpectation paperM (fun _ => w1X) succDeferral)
    (fun _ => payoutSchedule)

/-- W1's `A`: FAF's LIA over `w1Process` (a different process from `H`'s, hence a different
market).
Source: mandate W1
Kind: D
Fidelity: n/a -/
noncomputable abbrev w1A : History := liaHistory w1Process

/-- W1: the quote package (`li-quote-lane`'s mirror generator at the constant family `w1X`).
Source: mandate W1; `li-quote-lane` `crossQuotePackage_mirror`
Kind: L
Fidelity: variant (ledger-recorded determinacy)
Hyps: (a) none -/
theorem w1_pkg :
    CrossQuotePackage w1H w1Process succDeferral (fun _ => w1X) (fun n => ledgerLuv 0 n) :=
  crossQuotePackage_mirror paperM (fun _ => w1X) succDeferral (paperDP 𝗜𝚺₁)
    (fun _ => payoutSchedule)

/-- W1: `H` is a logical inductor over `paperDP 𝗜𝚺₁`.
Source: mandate W1; FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w1_inductorH : IsLogicalInductor w1H (paperDP 𝗜𝚺₁) :=
  LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)

/-- W1: `A` is a logical inductor over its ledger process.
Source: mandate W1; `li-quote-lane` `mirrorPair_inductor`
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem w1_inductorA : IsLogicalInductor w1A w1Process :=
  mirrorPair_inductor paperM (fun _ => w1X)
    (machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes _)) succDeferral
    (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) (fun _ => payoutSchedule) payoutSchedule_computable

/-- W1: every stage of `A`'s process is satisfiable.
Source: mandate W1; `li-quote-lane` `ledgerProcess_paperDP_hworld`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w1_hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (w1Process.D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- **W1 (N−). Theorem A with every hypothesis discharged on two real LIA markets:** for
`H = liaHistory (paperDP 𝗜𝚺₁)`, the fixed indicator `w1X`, and `A` the mirror-ledger LIA,
`Dominates (fun n => 𝔼^H_n(w1X)) (fun n => 𝔼^A_n(ledgerLuv 0 n))`. N−: non-degeneracy (a day
with `a_n ≠ Y_n`, or `𝔼^H_m(w1X) ≠ 𝔼^H_{m+1}(w1X)`) is not proved — LIA prices of an undecided
atom are not pinned by anything available; the instance with content is W2.
Source: mandate W1
Kind: N-
Fidelity: variant (as `crossQuotePackage_mirror`)
Hyps: (a) none -/
theorem theoremA_w1 :
    Dominates (fun n => w1X.expect w1H n) (quoteSeq (fun n => ledgerLuv 0 n) w1A) :=
  haveI := w1_inductorH
  haveI := w1_inductorA
  theoremA (A := w1A) w1X (indicatorOf_machineThresholdCodes _) (paperDP_hworld 𝗜𝚺₁)
    (indicatorOf_valued _ _) w1_hworldA w1_pkg

/-- W1: **the quote is a forecast, not a lookup** — the literal naming `H`'s day-`(n+1)`
expectation of `w1X` is absent from `A`'s schedule at day `n` (it enters at `n + 2`;
`li-quote-lane`'s `ledgerLuv_absent_before_payout`, the `cleanMirror_forecast` pattern checked at
this package's objects).
Source: `li-quote-lane` `cleanMirror_forecast`'s pattern at W1; audit r1 (fidelity) N12
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w1_forecast (n : ℕ) (r : ℚ) (b : Bool) :
    (ledgerFamily, ledgerPayload 0 n (Encodable.encode r), b) ∉
      (ledgerSchedule (realizedExpectation paperM (fun _ => w1X) succDeferral)
        (fun _ => payoutSchedule)).lits n :=
  ledgerLuv_absent_before_payout _ _ 0 n r b (by show n < n + 2; omega)

/-! ## W2: the decided case with content -/

/-- W2's `H`-process: `li-pseudorandom`'s `atomDP id x (·+1)`, which decides `atom k` at stage
`k + 1` with truth `x k`.
Source: mandate W2; `li-pseudorandom` `atomDP`
Kind: D
Fidelity: n/a -/
abbrev w2DP (x : ℕ → Bool) : DeductiveProcess := atomDP id x (fun j => j + 1)

/-- W2's `H`: FAF's LIA over `w2DP x`.
Source: mandate W2
Kind: D
Fidelity: n/a -/
noncomputable abbrev w2H (x : ℕ → Bool) : History := liaHistory (w2DP x)

/-- W2's fixed LUV: the indicator of `atom k`.
Source: mandate W2
Kind: D
Fidelity: n/a -/
noncomputable abbrev w2X (k : ℕ) : LUV := LUV.indicatorOf (Formula.atom k)

/-- W2: `H` is a logical inductor over `w2DP x` for primitive recursive `x`.
Source: mandate W2; `li-pseudorandom` `atomDP_succ_isLogicalInductor`
Kind: L
Fidelity: n/a
Hyps: (a) `hx` -/
theorem w2_inductorH {x : ℕ → Bool} (hx : Primrec x) : IsLogicalInductor (w2H x) (w2DP x) :=
  atomDP_succ_isLogicalInductor Primrec.id hx

/-- W2: every stage of `H`'s process is satisfiable (the atom world).
Source: mandate W2; `li-pseudorandom` `atomDP_hworld`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w2_hworldH (x : ℕ → Bool) : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((w2DP x).D n) :=
  atomDP_hworld Function.injective_id x _

/-- **W2: the determinacy of `w2X k` at `truthR x k` is derived**, from `li-pseudorandom`'s
`atomDP_theoryTruth` (the literal of `k` is in stage `k + 1`) and FAF's `IsIndicator.valuesAt`.
Source: mandate W2; root-fa-2-006
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem w2_determined (x : ℕ → Bool) (k : ℕ) :
    LUV.DeterminedVia (w2X k) (w2DP x) (truthR x k) := by
  intro v hv
  have h := atomDP_theoryTruth (a := id) (g := fun j => j + 1) (fun j => Nat.lt_succ_self j) x k
    v hv
  have h2 := (LUV.indicatorOf_isIndicator (Formula.atom k) (w2DP x)).valuesAt hv
  rw [← h]
  exact h2

/-- W2: `H`'s exact market program, read off the inductor certificate.
Source: none: infrastructure (W2)
Kind: D
Fidelity: n/a -/
noncomputable def w2M {x : ℕ → Bool} (hx : Primrec x) : MarketComputation (w2H x) :=
  (w2_inductorH hx).marketComputable.nonemptyComputation.some

/-- W2's `A`-process: `paperDP 𝗜𝚺₁` plus the ledger of `H`'s realized day-`(n+1)` expectations of
`w2X k`, published at `n + 2`.
Source: mandate W2
Kind: D
Fidelity: n/a -/
noncomputable abbrev w2Process {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) (realizedExpectation (w2M hx) (fun _ => w2X k) succDeferral)
    (fun _ => payoutSchedule)

/-- W2: the quote package.
Source: mandate W2; `li-quote-lane` `crossQuotePackage_mirror`
Kind: L
Fidelity: variant (ledger-recorded determinacy)
Hyps: (a) none -/
theorem w2_pkg {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    CrossQuotePackage (w2H x) (w2Process hx k) succDeferral (fun _ => w2X k)
      (fun n => ledgerLuv 0 n) :=
  crossQuotePackage_mirror (w2M hx) (fun _ => w2X k) succDeferral (paperDP 𝗜𝚺₁)
    (fun _ => payoutSchedule)

/-- W2: `A` is a logical inductor over its ledger process.
Source: mandate W2; `li-quote-lane` `mirrorPair_inductor`
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem w2_inductorA {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    IsLogicalInductor (liaHistory (w2Process hx k)) (w2Process hx k) :=
  mirrorPair_inductor (w2M hx) (fun _ => w2X k)
    (machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes _)) succDeferral
    (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) (fun _ => payoutSchedule) payoutSchedule_computable

/-- W2: every stage of `A`'s process is satisfiable.
Source: mandate W2
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem w2_hworldA {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((w2Process hx k).D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- **W2 (N+). The decided case of Theorem A with every hypothesis discharged and the limit
named:** for every primitive recursive stream `x` and every `k`, on `H = liaHistory (atomDP id x
(·+1))` and `A` the mirror-ledger LIA, both `𝔼^H_n(1(atom k)) → truthR x k` and the quote
`𝔼^A_n(ledgerLuv 0 n) → truthR x k`. A family of instances with non-constant streams, two
distinct real LIA markets, and the determinacy derived rather than assumed.
Source: mandate W2; root-fa-2-006
Kind: N+
Fidelity: variant (as `crossQuotePackage_mirror`)
Hyps: (a) `hx` -/
theorem decided_w2 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    Tendsto (fun n => (w2X k).expect (w2H x) n) atTop (𝓝 (truthR x k)) ∧
      Tendsto (quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k))) atTop
        (𝓝 (truthR x k)) :=
  haveI := w2_inductorH hx
  haveI := w2_inductorA hx k
  ⟨decided_expect_tendsto (H := w2H x) (w2X k) (indicatorOf_machineThresholdCodes _)
      (w2_hworldH x) (w2_determined x k),
    decided_quote_tendsto (A := liaHistory (w2Process hx k)) (w2X k)
      (indicatorOf_machineThresholdCodes _) (w2_hworldH x) (w2_determined x k)
      (w2_hworldA hx k) (w2_pkg hx k)⟩

/-- **W2 instantiates `theoremA` itself** (not only T7): every hypothesis of Theorem A —
`hcode`, `hworldH`, `hval` (from `indicatorOf_valued`), `hworldA`, `pkg` — discharged by W2's
objects, so the ledger's citation of W2 as `theoremA`'s N+ witness points at a real
instantiation. The content (`a_n → truthR x k` needs `A` to be an inductor over a process whose
ledger pins `Y_n` only two days late) is exercised.
Source: mandate W2; audit r1 (fidelity) N5
Kind: N+
Fidelity: variant (as `crossQuotePackage_mirror`)
Hyps: (a) `hx` -/
theorem theoremA_w2 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    Dominates (fun n => (w2X k).expect (w2H x) n)
      (quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k))) :=
  haveI := w2_inductorH hx
  haveI := w2_inductorA hx k
  theoremA (A := liaHistory (w2Process hx k)) (w2X k) (indicatorOf_machineThresholdCodes _)
    (w2_hworldH x) (indicatorOf_valued _ _) (w2_hworldA hx k) (w2_pkg hx k)

/-- W2: the quote is a forecast, not a lookup (as `w1_forecast`, at W2's ledger).
Source: `li-quote-lane` `cleanMirror_forecast`'s pattern at W2; audit r1 (fidelity) N12
Kind: L
Fidelity: n/a
Hyps: (a) `hx` -/
theorem w2_forecast {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) (n : ℕ) (r : ℚ) (b : Bool) :
    (ledgerFamily, ledgerPayload 0 n (Encodable.encode r), b) ∉
      (ledgerSchedule (realizedExpectation (w2M hx) (fun _ => w2X k) succDeferral)
        (fun _ => payoutSchedule)).lits n :=
  ledgerLuv_absent_before_payout _ _ 0 n r b (by show n < n + 2; omega)

/-! ## W3: Half 1's divergent gate at the market level -/

/-- **A sufficient condition for Half 1's `hdiv`, at grade (a):** if the quote converges to `L`
and `t + δ < L` (positive width), the upper gate `Ind_δ(a_n > t)` is a divergent weighting in
`A`'s realized prices — it is eventually `1`.
Source: [[faithful-acceleration-result]] §4.2 (the divergence step); mandate W3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem divergentWeighting_quoteRampAbove_of_tendsto {Y : ℕ → LUV} {A : History} {L : ℝ}
    (ha : Tendsto (quoteSeq Y A) atTop (𝓝 L)) {t δ : ℚ} (hδ : 0 < δ) (hL : (t : ℝ) + δ < L) :
    DivergentWeighting (quoteRampAbove Y t δ) A := by
  refine ⟨fun n => quoteRampAbove_mem_Icc Y hδ A n, ?_⟩
  apply tendsto_prefixSum_atTop_of_frequently_one (fun i => (quoteRampAbove_mem_Icc Y hδ A i).1)
  have hev : ∀ᶠ n in atTop, (t : ℝ) + δ ≤ quoteSeq Y A n := by
    have := (Metric.tendsto_nhds.1 ha) (L - (t + δ)) (by linarith)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff] at hn
    linarith [hn.2]
  exact hev.frequently.mono (fun n hn => ((quoteRampAbove_eq_one_iff Y hδ A n).2 (by linarith)).ge)

/-- **W3: a market-level divergent gate.** At W2 with `x k = true`, the gate
`Ind_{1/4}(a_n > 1/2)` of `A`'s own quote is divergent in `A`'s realized prices. N+ as a
witness that `half1`'s `hdiv` is satisfiable on a real market (the mandate's missing piece);
N− as a gate: it is eventually identically `1` (`w3_gate_eventually_one`), so it does no
selecting — the best available without an undecided target (F15).
Source: mandate W3
Kind: N-
Fidelity: exact
Hyps: (a) `hx`, `hk` -/
theorem w3_hdiv {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) (hk : x k = true) :
    DivergentWeighting (quoteRampAbove (fun n => ledgerLuv 0 n) (1 / 2) (1 / 4))
      (liaHistory (w2Process hx k)) := by
  have h := (decided_w2 hx k).2
  have h1 : truthR x k = 1 := by simp [truthR, hk]
  rw [h1] at h
  exact divergentWeighting_quoteRampAbove_of_tendsto h (by norm_num) (by push_cast; norm_num)

/-- **W3: Half 1 (T3) with every hypothesis discharged** on the W2 pair — a real inductor
`A`, a real quote package, and a divergent gate exhibited in `A`'s realized prices. **N+ for
the hypothesis package, N− for T3's content**: the gate is eventually `≡ 1` and both `a_n` and
`Y_n` tend to `1`, so the conclusion follows from `decided_w2` by the donor rule alone
(`half1_w3_from_convergence`) — the instance rules out "the hypotheses are contradictory", not
"the theorem says nothing here". A selecting instance needs an undecided target (F15).
Source: mandate W3; audit r1 (adversarial) B2
Kind: N-
Fidelity: variant (as `crossQuotePackage_mirror`)
Hyps: (a) `hx`, `hk` -/
theorem half1_w3 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) (hk : x k = true) :
    HasLimitPoint
      (weightedBias
        (fun i => (quoteRampAbove (fun n => ledgerLuv 0 n) (1 / 2) (1 / 4) i).denote
          (liaHistory (w2Process hx k)))
        (quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k)))
        (realized (w2H x) succDeferral (fun _ => w2X k))) 0 :=
  haveI := w2_inductorA hx k
  half1 (w2_pkg hx k) (w2_hworldA hx k) (1 / 2) (1 / 4) (w3_hdiv hx k hk)

/-- **W3's degeneracy record (i): the gate is eventually `1`** on every day — at W2 with
`x k = true` the quote tends to `1`, so `Ind_{1/4}(a_n > 1/2)` is `1` on every late day: the
gate selects every day and does no selecting.
Source: audit r1 (adversarial) B2, probe `W3GateDegenerate.lean`
Kind: N-
Fidelity: n/a
Hyps: (a) `hx`, `hk` -/
theorem w3_gate_eventually_one {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) (hk : x k = true) :
    ∀ᶠ n in atTop,
      (quoteRampAbove (fun n => ledgerLuv 0 n) (1 / 2) (1 / 4) n).denote
        (liaHistory (w2Process hx k)) = 1 := by
  have h := (decided_w2 hx k).2
  have h1 : truthR x k = 1 := by simp [truthR, hk]
  rw [h1] at h
  have hev : ∀ᶠ n in atTop, (3 / 4 : ℝ) ≤
      quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k)) n := by
    have := (Metric.tendsto_nhds.1 h) (1 / 8) (by norm_num)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, abs_sub_lt_iff] at hn
    linarith [hn.2]
  filter_upwards [hev] with n hn
  refine (quoteRampAbove_eq_one_iff _ (by norm_num) _ n).2 ?_
  push_cast
  linarith

/-- **W3's degeneracy record (ii): `half1_w3`'s conclusion without Half 1** — from `decided_w2`,
`decided_realized_tendsto` and `li-asymp-calc`'s donor rule (`weightedAverage_tendsto_zero`,
`hasLimitPoint_zero_of_tendsto`) alone: no `half1`, no `quote_unbiased`, no
`recurringunbiasednessexp` on the gate. This is the proof that the instance does not exercise
T3's gated-unbiasedness content.
Source: audit r1 (adversarial) B2, probe `W3GateDegenerate.lean`
Kind: N-
Fidelity: n/a
Hyps: (a) `hx`, `hk` -/
theorem half1_w3_from_convergence {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) (hk : x k = true) :
    HasLimitPoint
      (weightedBias
        (fun i => (quoteRampAbove (fun n => ledgerLuv 0 n) (1 / 2) (1 / 4) i).denote
          (liaHistory (w2Process hx k)))
        (quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k)))
        (realized (w2H x) succDeferral (fun _ => w2X k))) 0 := by
  haveI := w2_inductorH hx
  have h := (decided_w2 hx k).2
  have h1 : truthR x k = 1 := by simp [truthR, hk]
  rw [h1] at h
  have hdiv := w3_hdiv hx k hk
  have hY : Tendsto (realized (w2H x) succDeferral (fun _ => w2X k)) atTop (𝓝 1) := by
    have := decided_realized_tendsto (H := w2H x) (w2X k) (indicatorOf_machineThresholdCodes _)
      (w2_hworldH x) (w2_determined x k) succDeferral
    rwa [h1] at this
  have hsub : Tendsto (fun i =>
      quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k)) i -
        realized (w2H x) succDeferral (fun _ => w2X k) i) atTop (𝓝 0) := by
    simpa using h.sub hY
  unfold weightedBias
  exact hasLimitPoint_zero_of_tendsto
    (weightedAverage_tendsto_zero (fun i => (hdiv.1 i).1) hdiv.2 hsub)

/-! ## W4: Lemma P at a non-trivial generable day-set -/

/-- **W4: Lemma P along the even days** on the W2 pair: along the filter
`atTop ⊓ 𝓟 {n | (evenDays n).denote A = 1}` the quote tends to `truthR x k`. Every hypothesis of
`lemmaP` is discharged with `E := evenDays` (`evenDays_pgenerable`, `evenDays_01`) and `hY` the
all-days limit restricted to the filter. **N+ for the hypothesis package** (a non-constant
generable `{0,1}` day-set, two real LIA markets), **N− for the content**: the conclusion also
follows from `decided_w2` by `tendsto_inf_left`; a day-set on which `Y_n` converges but off
which it does not needs an undecided target (F16).
Source: mandate W4
Kind: N-
Fidelity: variant (as `crossQuotePackage_mirror`)
Hyps: (a) `hx` -/
theorem lemmaP_w4 {x : ℕ → Bool} (hx : Primrec x) (k : ℕ) :
    Tendsto (quoteSeq (fun n => ledgerLuv 0 n) (liaHistory (w2Process hx k)))
      (atTop ⊓ 𝓟 {n | (evenDays n).denote (liaHistory (w2Process hx k)) = 1})
      (𝓝 (truthR x k)) :=
  haveI := w2_inductorH hx
  haveI := w2_inductorA hx k
  lemmaP (A := liaHistory (w2Process hx k)) (w2_pkg hx k) (w2_hworldA hx k)
    evenDays_pgenerable (evenDays_01 _)
    (tendsto_inf_left (decided_realized_tendsto (H := w2H x) (w2X k)
      (indicatorOf_machineThresholdCodes _) (w2_hworldH x) (w2_determined x k) succDeferral))

end Cleanroom.Fa.FaTheoremA
