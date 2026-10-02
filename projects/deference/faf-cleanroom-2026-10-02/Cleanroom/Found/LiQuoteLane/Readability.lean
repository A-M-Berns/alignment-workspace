import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Feature
import LogicalInduction.Properties.AffineCoherence

/-!
# `li-quote-lane` · Readability: a market's estimate of a published number is that number (T3)

**L4 needs (L).** The mandate specified `readability` with hypotheses "(a) throughout — neither
(L) nor (S2)". That version is not provable and is expected false: the ledger LUV `α_{j,n}` is
determined at `a j n` by construction (T1.2), but a sequence of *decided* sentences whose truth
values no efficiently computable trader can select on need not be priced at its truth values —
the source's own [[route-sparse-schedule]] §5.3 says so ("if `D_H^n` decides a sequence of facts
no e.c. trader can select on, no trader profits from mispricing them, and the market may sit at
½ forever"), and [[theorem-ss-streamlined]] §5 states L4 "under (L)". Over FAF the obstruction is
concrete: every route to `𝔼^H_n(α_{j,n}) ≈ₙ a_n` goes through an affine sequence whose constant
term is `−a j n`, and a `PolySequence` must *emit* that constant (`const_poly`), which for a
general computable table is exactly (L). So:

* `readability_ofApprox` (the engine; [[route-recurring-ccee]] §2 Lemma 2.1, "ledger tracking",
  in its approximant form) carries `hz : PGenerableRat P ẑ` for *some* rational sequence `ẑ` with
  `ẑ_n − a_{j,n} → 0` — FAF's `def:ece`, "generable from `P`'s own prices and constants" — and is a
  composition of `affine_provind_theory_tendsto_zero` (`Properties/AffineCoherence.lean`) with
  T1.2, T1.3 and T1.5;
* `readability` (T3.1) is its instance at the exact approximant `ẑ = a_j` (hypothesis
  `hL : PGenerableRat P (fun n => a j n)`), and `readability_ofTendsto` its instance at a
  *constant* approximant: a table with a rational limit needs no generability at all;
* `readability_fails_without_generability` states the refutation of the (a)-only version as an
  OPEN conjecture (a computable table pseudorandom against FAF's e.c. traders; a time-hierarchy
  construction, out of scope).

**`hL` (and `hz`) is a modelling substitution (c) for the source's (L), not (L) itself.** The
source's (L) ([[route-sparse-schedule]] §2) enlarges `H`'s *trader class* to `Pᴸ` — polynomial
time with oracle access to the published sequence `(a_n)` — and leaves the table arbitrary; FAF's
`IsLogicalInductor` has one fixed class (`EfficientlyComputable`) and no relativized object
(mandate Known issue 2). `hL` keeps FAF's class and constrains the *table*: it must be a legal
feature of `P`'s own prices. It is the *counterpart* of (L) in the unrelativized class — the same
predicate (generability of the table) demanded of the plain class, which is stronger than (L) on
the table and silent on the class — and the two coincide only when the oracle is redundant, the
regime of [[route-sparse-schedule]] §5.2 ("the ledger device is unnecessary"). For the intended
instance (a LIA's quotes) `hL` is not available, while the source's L4 under (L) does apply at a
relativized `H⁺`. Fidelity of `readability` is therefore `variant: plain trader class` and its
row carries `(c) hL` (audit round 1, adversarial B1 / fidelity N1). Findings F2 records the
discrepancy with the mandate. Scope: one-way; per-day full limit.

**Where `hL` does work.** For a table with a rational limit the conclusion of `readability` holds
with no `hL` (`readability_ofTendsto`; audit round 2, fidelity B1), so a convergent table cannot
witness what `hL` buys. The witnesses in `Witnesses.lean` are graded accordingly: the oscillating
table `readability_unpair` (no limit; N+ for the statement as written) is the one on which `hL`
is load-bearing; `readability_harmonic` and `readability_twoPowInv` (tables converging to `0`)
inhabit the package over real objects but are N− for `readability` and N+ for
`readability_ofTendsto`. All are N− relative to the intended LIA-table instance.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- Adding a uniformly generated feature to the constant coordinate preserves `PolySequence`
(FAF's `PolySequence.addConstEF`, `Construction/LUV/Syntax.lean`, re-proved here so that this
file does not import that lane).
Source: none: infrastructure (FAF `PolySequence.addConstEF`)
Kind: L
Fidelity: n/a -/
noncomputable def polySequence_addConstEF {As : ℕ → AffineCombination}
    (hA : AffineCombination.PolySequence As) (g : ℕ → EF) (hg : PGenerableWeighting g) :
    AffineCombination.PolySequence (fun n => (As n).addConstEF (g n)) where
  termCount := hA.termCount
  coefficient := hA.coefficient
  sentence := hA.sentence
  termCount_poly := hA.termCount_poly
  const_poly := MachineSpliceStream.serialize_add hA.const_poly hg.polySeg
  coefficient_poly := hA.coefficient_poly
  sentence_poly := hA.sentence_poly
  terms_eq := hA.terms_eq
  const_rank := by
    intro n
    simp only [AffineCombination.addConstEF, EF.rank]
    exact Nat.max_le.mpr ⟨hA.const_rank n, hg.rank_le n⟩
  coefficient_rank := hA.coefficient_rank
  const_closed := by
    intro n ρ V
    simp only [AffineCombination.addConstEF, EF.denoteWith, EF.denote_add, Pi.add_apply]
    rw [hA.const_closed n ρ V, hg.closed n ρ V]
  coefficient_closed := hA.coefficient_closed

/-- **Lemma 2.1 (ledger tracking), the approximant form — the engine of T3.1:** for any inductor
`P` over the ledger process (every stage satisfiable, table in `[0,1]`), if some `P`-generable
rational sequence `ẑ` (FAF's `PGenerableRat`, the paper's `def:ece`) approximates item `j`'s
table — `ẑ_n − a_{j,n} → 0` — then the reader's day-`n` expectation of the ledger LUV tends to
the published number: `𝔼^P_n(α_{j,n}) ≈ₙ a_{j,n}`, per day, full limit. `readability` (T3.1) is
the case `ẑ = a_j` (exact approximant, `hL`); `readability_ofTendsto` the case of a constant
approximant (a table with a rational limit, no generability of the table at all).

Route: the affine sequence `A_n := mesh_n(α_{j,n}) − ⟨feature of ẑ_n⟩` is a `PolySequence`
(T1.3 for the mesh, `hz` for the constant); its prices are bounded (the approximation error is a
convergent, hence bounded, sequence); its completed-theory value is within
`1/(n+1) + |ẑ_n − a_{j,n}|` of `0` (T1.2 through `PCWorld.expectApprox_near_ofGrid`), which
vanishes; FAF's vanishing-error affine provability induction `affine_provind_theory_tendsto_zero`
gives `price → 0`, the price is `𝔼^P_n(α_{j,n}) − ẑ_n`, and `ẑ_n − a_{j,n} → 0` finishes.
Non-vacuity of the world quantifier is `hworld` (T1.5), lifted to the theory level by
`ledgerProcess_theoryWorld`.

**`hz` is a modelling substitution (c) for the source's (H⁺-CLASS)** — the source asks for a
`𝒞_{H⁺}`-machine (the relativized class) computing the approximants; FAF has one fixed trader
class, and `hz` demands generability of the approximant in it (the counterpart in the
unrelativized class; see `readability`'s docstring and the module docstring). The source's
determinacy hypothesis ("determined via `Γ_H` with values `z_n`") is T1.2 by construction.
Scope: one-way.
Source: [[route-recurring-ccee]] §2 Lemma 2.1 (vq-wiki-048 (d), "ledger tracking"); [[theorem-ss-streamlined]] §5 (L4); audit r2 fidelity non-blocking 1
Kind: C
Fidelity: variant: plain trader class — the source's `𝒞_{H⁺}`-computable approximants rendered as `P`-generability of the approximant (`hz`); the source's determinacy hypothesis is T1.2 by construction; the error bound `ε_n → 0` is `hlim`
Hyps: (c) `hz` — generability of the approximant in FAF's fixed class, in place of the source's relativized class `𝒞_{H⁺}`, which has no FAF object; all else (a) -/
theorem readability_ofApprox (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [hP : IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (zhat : ℕ → ℚ) (hz : PGenerableRat P zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) := by
  obtain ⟨feat, hfeat⟩ := hz
  have hneg : PGenerableWeighting (fun n => EF.mul (EF.const (-1)) (feat n)) :=
    PGenerableWeighting.mul (pgenerableWeighting_const (-1)) hfeat.toWeighting
  set As : ℕ → AffineCombination := fun n =>
    ((ledgerLuv j n).expectAffine (n + 1)).addConstEF (EF.mul (EF.const (-1)) (feat n)) with hAs
  have hpoly : AffineCombination.PolySequence As :=
    polySequence_addConstEF
      (LUV.expectAffineSeq_polySequence (fun n => ledgerLuv j n) (ledgerLuv_thresholdCodes j))
      _ hneg
  have hprices : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := ledgerProcess base a e) n φ
  have hconst : ∀ n, (EF.mul (EF.const (-1)) (feat n)).denote P = -(zhat n : ℝ) := by
    intro n
    simp [hfeat.denote n]
  have hvalue : ∀ n (w : Valuation),
      (As n).value P w = (ledgerLuv j n).expectApprox w (n + 1) - zhat n := by
    intro n w
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_value, LUV.expectAffine_value, hconst]
    ring
  have hprice : ∀ n, (As n).price P n = (ledgerLuv j n).expect P n - zhat n := by
    intro n
    rw [AffineCombination.price, hvalue]
    rfl
  -- the approximation error is bounded: a convergent real sequence is bounded
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, |(zhat n : ℝ) - a j n| ≤ B := by
    obtain ⟨B, hB⟩ := (hlim.abs).bddAbove_range
    exact ⟨B, fun n => hB (Set.mem_range_self n)⟩
  have hbounded : BoundedAffinePrices As P := by
    refine ⟨2 + B, ?_, fun n m => ?_⟩
    · have h0 := hB 0
      have h0' := abs_nonneg ((zhat 0 : ℝ) - a j 0)
      linarith
    rw [AffineCombination.price, hvalue]
    have h1 := (ledgerLuv j n).expectApprox_nonneg (P m) (n + 1) (fun s => (hprices m s).1)
    have h2 := (ledgerLuv j n).expectApprox_le_one (P m) (n + 1) (fun s => (hprices m s).2)
    have h3 : (0 : ℝ) ≤ a j n := by exact_mod_cast (hmem j n).1
    have h4 : (a j n : ℝ) ≤ 1 := by exact_mod_cast (hmem j n).2
    obtain ⟨h5, h6⟩ := abs_le.mp (hB n)
    rw [abs_le]
    constructor <;> linarith
  have hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C := by
    refine ⟨1, fun n => ?_⟩
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_magnitude]
    exact LUV.expectAffine_magnitude_le_one _ P _
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory (ledgerProcess base a e) → |(As n).value P v.payout| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim2 : Tendsto (fun n => |(zhat n : ℝ) - a j n|) atTop (𝓝 0) := by
      have := hlim.abs
      rwa [abs_zero] at this
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hlim2.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 v hv
    rw [hvalue]
    have hdet := ledgerLuv_determinedVia base a e hmem j n v hv
    have hgrid : ∀ i : ℕ, i < n + 1 →
        (((i : ℝ) / ((n + 1 : ℕ) : ℝ) < (a j n : ℝ) →
            v.Holds ((ledgerLuv j n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)))) ∧
          ((a j n : ℝ) < (i : ℝ) / ((n + 1 : ℕ) : ℝ) →
            ¬ v.Holds ((ledgerLuv j n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))))) := by
      intro i _
      have hc : (((i : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have := hdet.2.2 ((i : ℚ) / ((n + 1 : ℕ) : ℚ))
      rw [hc] at this
      exact this
    have hnear := PCWorld.expectApprox_near_ofGrid hdet.1 hdet.2.1 (Nat.succ_pos n) hgrid
    calc |(ledgerLuv j n).expectApprox v.payout (n + 1) - zhat n|
        = |((ledgerLuv j n).expectApprox v.payout (n + 1) - a j n) + ((a j n : ℝ) - zhat n)| := by
          congr 1
          ring
      _ ≤ |(ledgerLuv j n).expectApprox v.payout (n + 1) - a j n| + |(a j n : ℝ) - zhat n| :=
          abs_add_le _ _
      _ = |(ledgerLuv j n).expectApprox v.payout (n + 1) - a j n| + |(zhat n : ℝ) - a j n| := by
          rw [abs_sub_comm (a j n : ℝ) (zhat n : ℝ)]
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + |(zhat n : ℝ) - a j n| := by gcongr
      _ = 1 / ((n : ℝ) + 1) + |(zhat n : ℝ) - a j n| := by push_cast; rfl
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  have hlim0 := hpoly.affine_provind_theory_tendsto_zero P (ledgerProcess base a e) hbounded hmag
    hworld hval
  unfold AsympEq at hlim0 ⊢
  have h1 : Tendsto (fun n => (ledgerLuv j n).expect P n - zhat n) atTop (𝓝 0) := by
    refine hlim0.congr fun n => ?_
    dsimp only
    rw [hprice, sub_zero]
  have h3 := h1.add hlim
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-- **T3.1 (headline). L4, the readability collapse, with (L) rendered as `P`-generability of
the table:** for any inductor `P` over the ledger process (every stage satisfiable, table in
`[0,1]`), if the published table is `P`-generable (FAF's `PGenerableRat`, the paper's
`def:ece`: a legal feature of `P`'s own prices and constants denotes it), the reader's day-`n`
expectation of the ledger LUV tends to the published number: `𝔼^P_n(α_{j,n}) ≈ₙ a_{j,n}`, per
day, full limit.

Proof: the exact-approximant instance (`ẑ = a_j`) of `readability_ofApprox` (Lemma 2.1), whose
route is: the affine sequence `A_n := mesh_n(α_{j,n}) − ⟨feature of a_{j,n}⟩` is a `PolySequence`
(T1.3 for the mesh, `hL` for the constant); its completed-theory value is within `1/(n+1)` of
`0` (T1.2 through `PCWorld.expectApprox_near_ofGrid`); FAF's vanishing-error affine provability
induction `affine_provind_theory_tendsto_zero` gives `price → 0`, and the price is
`𝔼^P_n(α_{j,n}) − a_{j,n}`. Non-vacuity of the world quantifier is `hworld` (T1.5), lifted to the
theory level by `ledgerProcess_theoryWorld`.

**`hL` is a modelling substitution (c) for the source's (L).** [[theorem-ss-streamlined]] §5
states L4 "under (L)", and [[route-sparse-schedule]] §5.3 shows pointwise agreement fails
without it; but (L) is a *trader-class* hypothesis (`H ⊣ Pᴸ`, oracle access to `(a_n)`), which
has no FAF object, while `hL` is a *table* hypothesis in FAF's fixed class. `hL` is the
counterpart of (L) in the unrelativized class — the same predicate (generability of the table)
demanded of the plain class, stronger than (L) on the table and silent on the class — and the
two coincide only when the oracle is redundant ([[route-sparse-schedule]] §5.2). So this theorem
is L4 in the regime where the ledger is a stylistic choice, and does *not* apply to the LIA-table
pair of `PaperWitness.lean` (module docstring). The mandate's "(a) throughout" is corrected here
(findings F2); `readability_fails_without_generability` states the failure of the (a)-only
version. **Where `hL` does work:** a table with a rational limit needs no `hL`
(`readability_ofTendsto`), so the witness on which `hL` is load-bearing is the oscillating table
`readability_unpair` (`Witnesses.lean`; N+ for the statement as written); `readability_harmonic`
/ `readability_twoPowInv` inhabit the package over real objects with `hL` idle (N−). Scope:
one-way.
Source: [[theorem-ss-streamlined]] §5 (vq-wiki-051, L4 Proof A/B); [[route-sparse-schedule]] §2 (L), §5.2, §5.3; lean-deference-037
Kind: L (the exact-approximant instance of `readability_ofApprox`, Kind C, which carries the route)
Fidelity: variant: plain trader class — (L)'s oracle access to `a_n` rendered as `P`-generability of the table (`hL`), the counterpart of (L) in the unrelativized class; the source's (S2) is not needed (T1.2 supplies determinacy by construction)
Hyps: (c) `hL` — a hypothesis on the table in place of the source's relativized class `Pᴸ`, which has no FAF object; all else (a) -/
theorem readability (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [hP : IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (hL : PGenerableRat P (fun n => a j n)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  readability_ofApprox P base a e hworld hmem j (fun n => a j n) hL (by
    simp only [sub_self]
    exact tendsto_const_nhds)

/-- **Lemma 2.1 with machine-computed approximants:** the source's form — "a machine computes
rationals `ẑ_n` with `|ẑ_n − z_n| → 0`" — with the machine FAF's machine-metered rational code
stream (`MachineRatCodes`, the plain-class counterpart of the source's `𝒞_{H⁺}`-machine). A
corollary of `readability_ofApprox` through `PGenerableRat.ofMachineRatCodes`; the general form
also admits approximants that are price features of `P`. Scope: one-way.
Source: [[route-recurring-ccee]] §2 Lemma 2.1 (vq-wiki-048 (d))
Kind: L (instance of `readability_ofApprox`)
Fidelity: variant: plain trader class — the source's `𝒞_{H⁺}`-machine rendered as FAF's `MachineRatCodes`
Hyps: (c) `hz` (machine-metered codes for the approximant, in place of the source's relativized machine class); all else (a) -/
theorem readability_ofMachineApprox (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [hP : IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (zhat : ℕ → ℚ) (hz : MachineRatCodes zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  readability_ofApprox P base a e hworld hmem j zhat (PGenerableRat.ofMachineRatCodes hz P) hlim

/-- **L4 without (L), for a table with a rational limit:** if item `j`'s table converges to a
rational `L`, the reader's expectation of the ledger LUV tends to the published number with *no*
generability hypothesis on the table — the constant approximant `ẑ ≡ L` is generable for free
(`MachineRatCodes.const`). This is why a convergent table cannot witness what `hL` buys in
`readability` (audit round 2, fidelity B1): on such a table `hL` is idle. Scope: one-way.
Source: [[route-recurring-ccee]] §2 Lemma 2.1 at a constant approximant; audit r2 fidelity B1 (probe `FidelityConvergentTable.lean`, adopted)
Kind: L (the constant-approximant instance of `readability_ofApprox`)
Fidelity: n/a (a corollary; the source has no separate statement)
Hyps: (a) none (every hypothesis of `readability_ofApprox` other than the inductor, `hworld` and `hmem` is discharged) -/
theorem readability_ofTendsto (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [hP : IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) (L : ℚ)
    (hlim : Tendsto (fun n => (a j n : ℝ)) atTop (𝓝 (L : ℝ))) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  readability_ofApprox P base a e hworld hmem j (fun _ => L)
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const L) P) (by
      have := (tendsto_const_nhds (x := (L : ℝ))).sub hlim
      rwa [sub_self] at this)

/-- **OPEN (conjectured refutation of the mandate's (a)-only L4).** Some inductor over some ledger
process, with every stage satisfiable and a `[0,1]` table, does *not* price the ledger LUV at the
published number. The expected witness is a `[0,1]`-valued table with a decidable lower cut
`r ↦ decide (r < a j n)` (all that the statement's `processComputable` constrains; exact
identification of the rational from the cut is not demanded) that is pseudorandom against FAF's
`EfficientlyComputable` traders (the source's own argument, [[route-sparse-schedule]] §5.3: "the
market may sit at ½ forever"); exhibiting one is a time-hierarchy construction outside this
package's scope. A convergent table cannot be the witness (`readability_ofTendsto`). Recorded as
an open statement so that no dependent cites the (a)-only version as available. Scope: one-way.
Source: [[route-sparse-schedule]] §5.3; mandate T3.1 (corrected, findings F2)
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem readability_fails_without_generability :
    ∃ (base : DeductiveProcess) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (P : History)
      (j : ℕ), IsLogicalInductor P (ledgerProcess base a e) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n)) ∧
      (∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) ∧
      ¬ ((fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ))) := by
  sorry

/-- **T4.2, the ramp tracks the published number under `hL`:** the legal ramp of the ledger
price feature (`ledgerRamp_pgenerable`) converges to the ramp of the published number, per day.
Inherits `readability`'s hypothesis `hL` and its label (a (c) for the source's (L)).
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d), "R2 works iff `â_n → a_n`"); composition of `ledgerRamp_tracks` and `readability`
Kind: C
Fidelity: variant: plain trader class (as `readability`)
Hyps: (c) `hL` (as in `readability`); all else (a) -/
theorem ledgerRamp_tendsto (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (hL : PGenerableRat P (fun n => a j n)) {t δ : ℚ} (hδ : 0 < δ) :
    Tendsto (fun n => (ledgerRamp j t δ n).denote P - ctsInd δ (a j n) t) atTop (𝓝 0) := by
  have h := readability P base a e hworld hmem j hL
  unfold AsympEq at h
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ledgerRamp_tracks j hδ P a n) ?_
  have habs : Tendsto (fun n => |(ledgerLuv j n).expect P n - a j n|) atTop (𝓝 0) := by
    have := h.abs
    rwa [abs_zero] at this
  have := habs.div_const (δ : ℝ)
  rwa [zero_div] at this

/-- **T3.3, inside = outside, the outside half (Lemma 3):** scaling a LUV by the constant feature
`a j n` scales its expectation, with *no* generability of `a j n` needed to write the combination
(only to trade on it, T4.2). Restated from `li-asymp-calc`'s `scaleByFeature_expect`.
Source: [[route-sparse-schedule]] §8.1 Lemma 3 (vq-wiki-051)
Kind: L
Fidelity: exact (the outside reading; the inside reading `⌜X_n · u_n⌝` as one LUV is FAF's product lane and is not attempted)
Hyps: (a) none -/
theorem scaleByFeature_const_expect (u : ℚ) (X : LUV) (P : History) (n : ℕ) :
    (LUVCombination.scaleByFeature (EF.const u) X).expect P n = (u : ℝ) * X.expect P n := by
  rw [scaleByFeature_expect]
  simp

end Cleanroom.Found.LiQuoteLane
